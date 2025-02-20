/*******************************************************************************
 *
 * Copyright 2023 Portable Software Company
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 ******************************************************************************/

#include <windows.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <tchar.h>
#include "svc.h"

static SVCINFO serviceinfo;
static TCHAR *servicenamebuf;
static SERVICE_STATUS_HANDLE servicehandle;
static SERVICE_STATUS servicestatus;
static TCHAR serviceerror[512];
static int (*programmain)(int, TCHAR **);
static void (*programstop)(void);

static VOID WINAPI service_main(DWORD, LPTSTR *);
static VOID WINAPI service_ctrl(DWORD);
static int reportstatus(DWORD, DWORD);


int svcinstall(SVCINFO *info, TCHAR *user, TCHAR *password, int argc, TCHAR **argv)
{
	int i1, i2, rc, seconds;
	DWORD checkpoint;
	TCHAR path[MAX_PATH + 256], userwork[128], *pathptr;
	SC_HANDLE manager, service;

	if (info == NULL || info->servicename == NULL || !info->servicename[0] ||
	    info->servicedisplayname == NULL || !info->servicedisplayname[0]) {
		_tcscpy(serviceerror, _T("svcinstall() failed: service name information required"));
		return -1;
	}

	if (user != NULL) {
		if (*user) {
			for (i1 = 0; user[i1] && user[i1] != '\\'; i1++);
			if (!user[i1]) {
				userwork[0] = (TCHAR) '.';
				userwork[1] = (TCHAR) '\\';
				_tcscpy(userwork + 2 * sizeof(TCHAR), user);
				user = userwork;
			}
			if (password != NULL && !*password) password = NULL;
		}
		else password = user = NULL;
	}
	else password = NULL;

	if (!GetModuleFileName(NULL, path + 1, sizeof(path) - 2)) {
		if (argc < 1) {
			_stprintf(serviceerror, _T("GetModuleFileName() failed, error = %d\n"), (int) GetLastError());
			return -1;
		}
		_tcscpy(path + 1, argv[0]);
	}
	/* if path contains a space, must surround with quotes */
	for (i1 = 1; path[i1] && !isspace(path[i1]); i1++);
	if (path[i1]) {
		path[0] = (TCHAR) '"';
		_tcscat(path, _T("\""));
		pathptr = path;
	}
	else pathptr = path + 1;
	for (i1 = 0; ++i1 < argc; ) {  /* append any arguments */
		/* if arg contains a space, must surround with quotes (assumes arg does not have a quote) */
		for (i2 = 0; argv[i1][i2] && !isspace(argv[i1][i2]); i2++);
		if (argv[i1][i2]) _tcscat(pathptr, _T(" \""));
		else _tcscat(pathptr, _T(" "));
		_tcscat(pathptr, argv[i1]);
		if (argv[i1][i2]) _tcscat(pathptr, _T("\""));
	}

	rc = 0;
	manager = OpenSCManager(NULL, NULL, SC_MANAGER_CREATE_SERVICE);
	if (manager) {
		service = OpenService(manager, info->servicename, SERVICE_ALL_ACCESS);
		if (service) {
			if (QueryServiceStatus(service, &servicestatus)) {
				if (servicestatus.dwCurrentState != SERVICE_STOPPED) {
					if (ControlService(service, SERVICE_CONTROL_STOP, &servicestatus)) {
						for (seconds = -1; ; seconds--) {
							if (!QueryServiceStatus(service, &servicestatus)) break;
							if (servicestatus.dwCurrentState != SERVICE_STOP_PENDING) break;
							if (!seconds && checkpoint >= servicestatus.dwCheckPoint) break;
							if (seconds <= 0 || checkpoint < servicestatus.dwCheckPoint) {
								checkpoint = servicestatus.dwCheckPoint;
								seconds = (int)(servicestatus.dwWaitHint / 1000 + 1);
							}
							Sleep(1000);
						}
					}
				}
			}
			DeleteService(service);
			CloseServiceHandle(service);
		}
		service = CreateService(manager, info->servicename, info->servicedisplayname,
			SERVICE_ALL_ACCESS, SERVICE_WIN32_OWN_PROCESS, SERVICE_AUTO_START, SERVICE_ERROR_NORMAL,
			pathptr, NULL, NULL, NULL, user, password);
		if (service) CloseServiceHandle(service);
		else {
			_stprintf(serviceerror, _T("CreateService() failed, error = %d\n"), (int) GetLastError());
			rc = -1;
		}
		CloseServiceHandle(manager);
	}
	else {
		_stprintf(serviceerror, _T("OpenSCManager() failed, error = %d\n"), (int) GetLastError());
		rc = -1;
	}
	return rc;
}

int svcremove(SVCINFO *info)
{
	int rc, seconds;
	DWORD checkpoint;
	SC_HANDLE manager, service;

	if (info == NULL || info->servicename == NULL || !info->servicename[0]) {
		_tcscpy(serviceerror, _T("svcremove() failed: service name information required"));
		return -1;
	}

	rc = 0;
	manager = OpenSCManager(NULL, NULL, SC_MANAGER_ALL_ACCESS);
	if (manager) {
		service = OpenService(manager, info->servicename, SERVICE_ALL_ACCESS);
		if (service) {
			if (QueryServiceStatus(service, &servicestatus)) {
				if (servicestatus.dwCurrentState != SERVICE_STOPPED) {
					if (ControlService(service, SERVICE_CONTROL_STOP, &servicestatus)) {
						for (seconds = -1; ; seconds--) {
							if (!QueryServiceStatus(service, &servicestatus)) break;
							if (servicestatus.dwCurrentState != SERVICE_STOP_PENDING) break;
							if (!seconds && checkpoint >= servicestatus.dwCheckPoint) break;
							if (seconds <= 0 || checkpoint < servicestatus.dwCheckPoint) {
								checkpoint = servicestatus.dwCheckPoint;
								seconds = (int)(servicestatus.dwWaitHint / 1000 + 1);
							}
							Sleep(1000);
						}
					}
				}
			}
			if (!DeleteService(service)) {
				_stprintf(serviceerror, _T("DeleteService() failed, error = %d\n"), (int) GetLastError());
				rc = -1;
			}
			CloseServiceHandle(service);
		}
		else {
			rc = GetLastError();
			if (rc != ERROR_SERVICE_DOES_NOT_EXIST) {
				_stprintf(serviceerror, _T("OpenService() failed, error = %d\n"), rc);
				rc = -1;
			}
			else rc = 1;
		}
		CloseServiceHandle(manager);
	}
	else {
		_stprintf(serviceerror, _T("OpenSCManager() failed, error = %d\n"), (int) GetLastError());
		rc = -1;
	}
	return rc;
}

int svcstart(SVCINFO *info)
{
	int rc, seconds;
	DWORD checkpoint;
	SC_HANDLE manager, service;

	if (info == NULL || info->servicename == NULL || !info->servicename[0]) {
		_tcscpy(serviceerror, _T("svcstart() failed: service name information required"));
		return -1;
	}

	rc = 0;
	manager = OpenSCManager(NULL, NULL, SC_MANAGER_CREATE_SERVICE);
	if (manager) {
		service = OpenService(manager, info->servicename, SERVICE_ALL_ACCESS);
		if (service) {
			if (QueryServiceStatus(service, &servicestatus)) {
				if (servicestatus.dwCurrentState != SERVICE_STOPPED) {
					if (ControlService(service, SERVICE_CONTROL_STOP, &servicestatus)) {
						for (seconds = -1; ; seconds--) {
							if (!QueryServiceStatus(service, &servicestatus)) break;
							if (servicestatus.dwCurrentState != SERVICE_STOP_PENDING) break;
							if (!seconds && checkpoint >= servicestatus.dwCheckPoint) break;
							if (seconds <= 0 || checkpoint < servicestatus.dwCheckPoint) {
								checkpoint = servicestatus.dwCheckPoint;
								seconds = (int)(servicestatus.dwWaitHint / 1000 + 1);
							}
							Sleep(1000);
						}
					}
				}
			}
			if (StartService(service, 0, NULL)) {
				for (seconds = -1; ; seconds--) {
					if (!QueryServiceStatus(service, &servicestatus)) {
						_stprintf(serviceerror, _T("QueryServiceStatus() failed, error = %d\n"), (int) GetLastError());
						rc = -1;
						break;
					}
					if (servicestatus.dwCurrentState == SERVICE_RUNNING) break;
					if (servicestatus.dwCurrentState == SERVICE_STOPPED) {
						rc = 1;
						break;
					}
					if (!seconds && checkpoint >= servicestatus.dwCheckPoint) {
						_stprintf(serviceerror, _T("service not started:\n   Current State: %d\n   Check Point: %d\n   Wait Hint: %d"),
							(int) servicestatus.dwCurrentState, (int) servicestatus.dwCheckPoint, (int) servicestatus.dwWaitHint);
						rc = -1;
						break;
					}
					if (seconds <= 0 || checkpoint < servicestatus.dwCheckPoint) {
						checkpoint = servicestatus.dwCheckPoint;
						seconds = (int)(servicestatus.dwWaitHint / 1000 + 1);
					}
					Sleep(1000);
				}
			}
			else {
				_stprintf(serviceerror, _T("StartService() failed, error = %d\n"), (int) GetLastError());
				rc = -1;
			}
			CloseServiceHandle(service);
		}
		else {
			_stprintf(serviceerror, _T("OpenService() failed, error = %d\n"), (int) GetLastError());
			rc = -1;
		}
		CloseServiceHandle(manager);
	}
	else {
		_stprintf(serviceerror, _T("OpenSCManager() failed, error = %d\n"), (int) GetLastError());
		rc = -1;
	}
	return rc;
}

int svcstop(SVCINFO *info)
{
	int rc, seconds;
	DWORD checkpoint;
	SC_HANDLE manager, service;

	if (info == NULL || info->servicename == NULL || !info->servicename[0]) {
		_tcscpy(serviceerror, _T("svcstop() failed: service name information required"));
		return -1;
	}

	rc = 0;
	manager = OpenSCManager(NULL, NULL, SC_MANAGER_ALL_ACCESS);
	if (manager) {
		service = OpenService(manager, info->servicename, SERVICE_ALL_ACCESS);
		if (service) {
			if (!QueryServiceStatus(service, &servicestatus)) {
				_stprintf(serviceerror, _T("QueryServiceStatus() failed, error = %d\n"), (int) GetLastError());
				rc = -1;
			}
			if (servicestatus.dwCurrentState == SERVICE_STOPPED) rc = 1;
			else if (ControlService(service, SERVICE_CONTROL_STOP, &servicestatus)) {
				for (seconds = -1; ; seconds--) {
					if (!QueryServiceStatus(service, &servicestatus)) {
						_stprintf(serviceerror, _T("QueryServiceStatus() failed, error = %d\n"), (int) GetLastError());
						rc = -1;
						break;
					}
					if (servicestatus.dwCurrentState != SERVICE_STOP_PENDING) break;
					if (!seconds && checkpoint >= servicestatus.dwCheckPoint) {
						_stprintf(serviceerror, _T("service not stopped:\n   Current State: %d\n   Check Point: %d\n   Wait Hint: %d"),
							(int) servicestatus.dwCurrentState, (int) servicestatus.dwCheckPoint, (int) servicestatus.dwWaitHint);
						rc = -1;
						break;
					}
					if (seconds <= 0 || checkpoint < servicestatus.dwCheckPoint) {
						checkpoint = servicestatus.dwCheckPoint;
						seconds = (int)(servicestatus.dwWaitHint / 1000 + 1);
					}
					Sleep(1000);
				}
			}
			else {
				rc = GetLastError();
				if (rc != ERROR_SERVICE_NOT_ACTIVE) {
					_stprintf(serviceerror, _T("ControlService() failed, error = %d\n"), rc);
					rc = -1;
				}
				else rc = 1;
			}
			CloseServiceHandle(service);
		}
		else {
			_stprintf(serviceerror, _T("OpenService() failed, error = %d\n"), (int) GetLastError());
			rc = -1;
		}
		CloseServiceHandle(manager);
	}
	else {
		_stprintf(serviceerror, _T("OpenSCManager() failed, error = %d\n"), (int) GetLastError());
		rc = -1;
	}
	return rc;
}

void svcrun(SVCINFO *info, int (*progmain)(int, TCHAR **), void (*progstop)(void))
{
	int i1, i2;
	SERVICE_TABLE_ENTRY dispatchtable[] = {
		{ NULL, (LPSERVICE_MAIN_FUNCTION) service_main },
		{ NULL, NULL }
	};

	programmain = progmain;
	programstop = progstop;

	if (info == NULL || info->servicename == NULL || !info->servicename[0] ||
	    info->servicedisplayname == NULL || !info->servicedisplayname[0]) {
		svclogerror(_T("svcrun() failed: service name information required"), 0);
		return;
	}
	i1 = (INT)wcslen(info->servicename) + 1;
	i2 = (INT)wcslen(info->servicedisplayname) + 1;
	servicenamebuf = malloc(i1 + i2);
	if (servicenamebuf == NULL) {
		svclogerror(_T("svcrun() failed: unable to allocate memory"), 0);
		return;
	}
	memcpy(servicenamebuf, info->servicename, i1);
	memcpy(servicenamebuf + i1, info->servicedisplayname, i2);
	serviceinfo.servicename = servicenamebuf;
	serviceinfo.servicedisplayname = servicenamebuf + i1;

	dispatchtable[0].lpServiceName = serviceinfo.servicename;
	if (!StartServiceCtrlDispatcher(dispatchtable))
		svclogerror(_T("StartServiceCtrlDispatcher() failed"), (int) GetLastError());
}

int svcisstarting(SVCINFO *info)
{
	int startingflag;
	SC_HANDLE manager, service;

	if (info == NULL || info->servicename == NULL || !info->servicename[0]) return FALSE;

	startingflag = FALSE;
	manager = OpenSCManager(NULL, NULL, SC_MANAGER_ALL_ACCESS);
	if (manager) {
		service = OpenService(manager, info->servicename, SERVICE_ALL_ACCESS);
		if (service) {
			if (QueryServiceStatus(service, &servicestatus)) {
				if (servicestatus.dwCurrentState == SERVICE_START_PENDING) startingflag = TRUE;
			}
			CloseServiceHandle(service);
		}
		CloseServiceHandle(manager);
	}
	return startingflag;
}

void svcstatus(int type, int waittime)
{
	DWORD statustype;

	if (!servicehandle) return;
	if (type == SVC_STARTING) statustype = SERVICE_START_PENDING;
	else if (type == SVC_STOPPING) statustype = SERVICE_STOP_PENDING;
	else if (type == SVC_RUNNING) statustype = SERVICE_RUNNING;
	else if (type == SVC_STOPPED) statustype = SERVICE_STOPPED;
	else return;
	reportstatus(statustype, (DWORD) waittime);
}

void svclogerror(TCHAR *errormsg, int errornum)
{
	int i1;
	TCHAR num[128], *servicename;
	LPTSTR strings[2];
	HANDLE eventsource;

	if (serviceinfo.servicename == NULL || !serviceinfo.servicename[0]) servicename = _T("DBCService");
	else servicename = serviceinfo.servicename;

	i1 = 0;
	if (errormsg != NULL && *errormsg) strings[i1++] = errormsg;
	if (errornum) {
		memcpy(num, _T("error = "), 8 * sizeof(TCHAR));
		_itot(errornum, num + 8 * sizeof(TCHAR), 10);
		strings[i1++] = num;
	}
	if (i1) {
		eventsource = RegisterEventSource(NULL, servicename);
		if (eventsource != NULL) {
			ReportEvent(eventsource, EVENTLOG_ERROR_TYPE, 0, 0, NULL, (WORD) i1, 0, (const TCHAR **) strings, NULL);
			DeregisterEventSource(eventsource);
		}
	}
}

void svcloginfo(TCHAR *msg)
{
	int i1 = 0;
	TCHAR *servicename;
	LPTSTR strings[1];
	HANDLE eventsource;

	if (serviceinfo.servicename == NULL || !serviceinfo.servicename[0]) servicename = _T("DBCService");
	else servicename = serviceinfo.servicename;

	if (msg != NULL && *msg) strings[i1++] = msg;
	eventsource = RegisterEventSource(NULL, servicename);
	if (eventsource != NULL) {
		ReportEvent(eventsource, EVENTLOG_INFORMATION_TYPE,
				0,		// Category
				0,		// Event ID
				NULL,	// Pointer to current user's security identifier (sid)
				(WORD) i1,	// number of strings in the array
				0,		// number of bytes of event specific data
				(const TCHAR **) strings,
				NULL		// Pointer to a buffer containing event specific data
				);
		DeregisterEventSource(eventsource);
	}
}

TCHAR *svcgeterror()
{
	return serviceerror;
}

static void WINAPI service_main(DWORD argc, LPTSTR *argv)
{
	/* register the service control handler */
	servicehandle = RegisterServiceCtrlHandler(serviceinfo.servicename, service_ctrl);
	if (servicehandle) {
		servicestatus.dwServiceType = SERVICE_WIN32_OWN_PROCESS;
		servicestatus.dwWin32ExitCode = 0;
		servicestatus.dwServiceSpecificExitCode = 0;

		/* do an initial start pending for 2 second */
		if (reportstatus(SERVICE_START_PENDING, 2000) && programmain != NULL) programmain(argc, argv);
		reportstatus(SERVICE_STOPPED, 0);
	}
	else svclogerror(_T("RegisterServiceCtrlHandler() failed"), GetLastError());
}

VOID WINAPI service_ctrl(DWORD controlcode)
{
	/* handle the requested control code */
	switch (controlcode) {
		case SERVICE_CONTROL_STOP:
		case SERVICE_CONTROL_SHUTDOWN:
			if (programstop != NULL) programstop();
			return;
		case SERVICE_CONTROL_PAUSE:
			break;
		case SERVICE_CONTROL_CONTINUE:
			break;
		case SERVICE_CONTROL_INTERROGATE:
			break;
	}
}

static int reportstatus(DWORD currentstate, DWORD waittime)
{
	static DWORD checkpoint = 0;
	int result;

	servicestatus.dwCurrentState = currentstate;
	if (currentstate == SERVICE_START_PENDING) servicestatus.dwControlsAccepted = 0;
	else servicestatus.dwControlsAccepted = SERVICE_ACCEPT_STOP | SERVICE_ACCEPT_SHUTDOWN;
	if (currentstate == SERVICE_RUNNING || currentstate == SERVICE_STOPPED) servicestatus.dwCheckPoint = 0;
	else servicestatus.dwCheckPoint = ++checkpoint;
	servicestatus.dwWaitHint = waittime;

	if (!(result = SetServiceStatus(servicehandle, &servicestatus)))
		svclogerror(_T("SetServiceStatus() failed"), GetLastError());
	return result;
}
