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

#define INC_STDIO
#define INC_STRING
#define INC_CTYPE
#define INC_STDLIB
#define INC_LIMITS
#define INC_ERRNO
#define INC_TIME
#include "includes.h"

#include "fio.h"

INT fioaoperr = 0;		/* variable to hold open errors */
INT fioalkerr = 0;		/* variable to hold lock errors */
INT fioaclerr = 0;		/* variable to hold close errors */
INT fioarderr = 0;		/* variable to hold read errors */
INT fioawrerr = 0;		/* variable to hold write errors */
INT fioaskerr = 0;		/* variable to hold seek errors */
INT fioaflerr = 0;		/* variable to hold flush errors */
INT fioatrerr = 0;		/* variable to hold truncate errors */
INT fioadlerr = 0;		/* variable to hold delete errors */

static INT fioaflags;
static OFFSET fileoffset = 0x7FFFFFF0;  //‭2,147,483,632‬
static OFFSET recoffset = 0x40000000;
static DWORD lockretrytime;
static TCHAR findfile[MAX_NAMESIZE + 1];
static FHANDLE findhandle = INVALID_HANDLE_VALUE;
static WIN32_FIND_DATA finddta;
static INT findpathlength;
static TCHAR foundfile[MAX_NAMESIZE + 1];
static INT matchname(TCHAR *name, TCHAR *pattern);

INT fioainit(INT *fioflags, FIOAINITSTRUCT *parms)
{
	fioaflags = *fioflags;
	fileoffset = parms->fileoffset;
	recoffset = parms->recoffset;
	lockretrytime = (DWORD) parms->lockretrytime;
	return(0);
}

/**
 * Returns zero if successful. If not, returns one of the ERR_xxxxx codes from fio.h
 */
INT fioaopen(TCHAR *filename, INT mode, INT type, FHANDLE *handle)
{
	/* following tables correspond to with each row representing the 9 open modes */
	/* in order and the columns representing fioxop:create = 0, fioxop:create = 1 */
	/* and fiotouch respectively */
	static DWORD openarg1[10][3] = {
		GENERIC_READ,					(DWORD) -1,				GENERIC_READ,
		GENERIC_READ,					(DWORD) -1,				GENERIC_READ,
		GENERIC_READ | GENERIC_WRITE,	(DWORD) -1,				GENERIC_READ | GENERIC_WRITE,
		GENERIC_READ,					(DWORD) -1,				GENERIC_READ,
		GENERIC_READ | GENERIC_WRITE,	(DWORD) -1,				GENERIC_READ | GENERIC_WRITE,
		GENERIC_READ | GENERIC_WRITE,	(DWORD) -1,				GENERIC_READ | GENERIC_WRITE,
		GENERIC_READ | GENERIC_WRITE,	GENERIC_READ | GENERIC_WRITE,	GENERIC_READ | GENERIC_WRITE,
		GENERIC_READ | GENERIC_WRITE,	GENERIC_READ | GENERIC_WRITE,	GENERIC_READ | GENERIC_WRITE,
		GENERIC_READ | GENERIC_WRITE,	GENERIC_READ | GENERIC_WRITE,	GENERIC_READ | GENERIC_WRITE,
		GENERIC_READ | GENERIC_WRITE,	GENERIC_READ | GENERIC_WRITE,	GENERIC_READ | GENERIC_WRITE
	};
	static DWORD openarg2[10][3] = {
		FILE_SHARE_READ,					(DWORD) -1,	FILE_SHARE_READ,
		FILE_SHARE_READ | FILE_SHARE_WRITE,	(DWORD) -1,	FILE_SHARE_READ | FILE_SHARE_WRITE,
		FILE_SHARE_READ | FILE_SHARE_WRITE,	(DWORD) -1,	FILE_SHARE_READ | FILE_SHARE_WRITE,
		0,									(DWORD) -1,	0,
		0,									(DWORD) -1,	0,
		0,									(DWORD) -1,	0,
		0,									0,			0,
		0,									0,			0,
		0,									0,			0,
		0,									0,			0
	};
	static DWORD openarg3[10][3] = {
		OPEN_EXISTING,	(DWORD) -1,		OPEN_EXISTING,
		OPEN_EXISTING,	(DWORD) -1,		OPEN_EXISTING,
		OPEN_EXISTING,	(DWORD) -1,		OPEN_EXISTING,
		OPEN_EXISTING,	(DWORD) -1,		OPEN_EXISTING,
		OPEN_EXISTING,	(DWORD) -1,		OPEN_EXISTING,
		OPEN_EXISTING,	(DWORD) -1,		OPEN_EXISTING,
		OPEN_EXISTING,	CREATE_ALWAYS,	OPEN_EXISTING,
		OPEN_EXISTING,	CREATE_ALWAYS,	OPEN_EXISTING,
		OPEN_EXISTING,	CREATE_NEW,		OPEN_EXISTING,
		OPEN_EXISTING,	OPEN_ALWAYS,	OPEN_EXISTING
	};
	INT i1;
	DWORD err;
	FHANDLE hndl;
	TCHAR workname[MAX_NAMESIZE + 1];

	if (fioaflags & FIO_FLAG_SINGLEUSER) {
		if (mode == FIO_M_SHR) mode = FIO_M_EXC;
		/*
		 * This call is under single user mode via config file and NOT the special SU build, the following line should happen
		 */
		else if (mode <= FIO_M_SRA) mode = FIO_M_ERO;
	}
	for (i1 = 0; filename[i1]; i1++) {
		if (filename[i1] == (TCHAR) '/') workname[i1] = (TCHAR) '\\';
		else workname[i1] = filename[i1];
	}
	workname[i1] = (TCHAR) '\0';

	hndl = CreateFile((LPTSTR) workname, openarg1[mode - 1][type], openarg2[mode - 1][type],
			NULL, openarg3[mode - 1][type], FILE_ATTRIBUTE_NORMAL, 0);
	if (hndl != INVALID_HANDLE_VALUE) {
		if (!type) {
			if (mode == FIO_M_EFC) {
				CloseHandle(hndl);
				return(ERR_EXIST);
			}
/*** DO THIS INSTEAD OF OPENING WITH TRUNCATE_EXISTING BECAUSE OF BUG WITH ***/
/*** NT WORKSTATION RUNNING ON NT SERVER ***/
			if (mode == FIO_M_PRP || mode == FIO_M_MTC) {
				if (!SetEndOfFile(hndl)) {
					fioawrerr = GetLastError();
					CloseHandle(hndl);
					return(ERR_WRERR);
				}
			}
		}
/*** THIS IS DONE TO FOOL MICROSOFT CLIENT FROM SUPPORTING LOCAL CACHE ***/
		if ((mode == FIO_M_SHR || mode == FIO_M_SRA) && !(fioaflags & FIO_FLAG_SINGLEUSER) && !fioalock(hndl, FIOA_WRLCK, fileoffset + 4, 0))
			fioalock(hndl, FIOA_UNLCK, fileoffset + 4, 0);
		*handle = hndl;
		return 0;
	}

	err = GetLastError();
	switch(err) {
		case ERROR_FILE_NOT_FOUND:
		case ERROR_PATH_NOT_FOUND:
		case ERROR_INVALID_DRIVE:
		case ERROR_NOT_READY:
			return(ERR_FNOTF);
		case ERROR_ACCESS_DENIED:
		case ERROR_SHARING_VIOLATION:
		case ERROR_NETWORK_ACCESS_DENIED:
			return(ERR_NOACC);
		case ERROR_FILE_EXISTS:
			return(ERR_EXIST);
		case ERROR_TOO_MANY_OPEN_FILES:
/*** WHAT IS "ERROR_NO_MORE_FILES" ? ***/
			return(ERR_EXCMF);
		case ERROR_INVALID_NAME:
		case ERROR_BAD_PATHNAME:
		case ERROR_BUFFER_OVERFLOW:
		case ERROR_BAD_NETPATH:
			return(ERR_BADNM);
		default:
			if (err) fioaoperr = err;
			else fioaoperr = 0x7FFFFFFF;
			return(ERR_OPERR);
	}
}

INT fioaclose(FHANDLE handle)
{
	if (!CloseHandle(handle)) {
		fioaclerr = GetLastError();
		return(ERR_CLERR);
	}
	return(0);
}

/**
 * Can return ERR_RDERR, ERR_SKERR, or 0
 * Does not move memory
 */
INT fioaread(FHANDLE handle, UCHAR *buffer, INT nbyte, OFFSET offset, INT *bytes)
{
	INT i1;
	DWORD cnt;

	if (offset != -1 && (i1 = fioalseek(handle, offset, 0, NULL))) return(i1);

	if (!ReadFile(handle, (LPVOID) buffer, (DWORD) nbyte, &cnt, NULL)) {
		fioarderr = GetLastError();
		return(ERR_RDERR);
	}
	if (bytes != NULL) *bytes = (INT) cnt;
	return(0);
}

/**
 * Does not move memory
 * May return 0 or ERR_WRERR, ERR_SKERR
 */
INT fioawrite(FHANDLE handle, UCHAR *buffer, size_t nbyte, OFFSET offset, size_t *bytes)
{
	INT i1;
	DWORD cnt;

	if (!nbyte) return(0);

	if (bytes != NULL) *bytes = 0;
	if (offset != -1 && (i1 = fioalseek(handle, offset, 0, NULL))) return(i1);

	if (!WriteFile(handle, (LPVOID) buffer, (DWORD) nbyte, (LPDWORD) &cnt, NULL)) {
		fioawrerr = GetLastError();
		return(ERR_WRERR);
	}
	if (bytes != NULL) *bytes = (INT) cnt;
	if ((DWORD) nbyte != cnt) {
		fioawrerr = -1;
		return(ERR_WRERR);
	}
	return(0);
}

/**
 * Can return 0 or ERR_SKERR (-50)
 * Does not move memory
 */
INT fioalseek(FHANDLE handle, OFFSET offset, INT method, OFFSET *filepos)
{
	LONG highoffset;
	DWORD pos, movemethod;

	if (method == 0) movemethod = FILE_BEGIN;
	else if (method == 1) movemethod = FILE_CURRENT;
	else if (method == 2) movemethod = FILE_END;
	else {
		fioaskerr = (0 - method);
		return(ERR_SKERR);
	}

	highoffset = (DWORD)(offset >> 32);
	pos = SetFilePointer(handle, (LONG)((DWORD) offset), &highoffset, movemethod);
	if (pos == INVALID_SET_FILE_POINTER) {
		fioaskerr = GetLastError();
		if (fioaskerr != NO_ERROR) return(ERR_SKERR);
	}
	if (filepos != NULL) *filepos = ((OFFSET) highoffset << 32) + pos;
	return(0);
}

/**
 * Does not move memory
 * Might return 0 or ERR_LKERR(-41), ERR_NOACC(-23)
 */
INT fioalock(FHANDLE handle, INT type, OFFSET offset, INT timeout)
{
	time_t time1;

	if (type & FIOA_FLLCK) offset = fileoffset;
	else if (type & FIOA_RCLCK) offset += recoffset;

	if (type & (FIOA_WRLCK | FIOA_RDLCK)) {
		time1 = 0;
		for ( ; ; ) {
			if (!LockFile(handle, (DWORD) offset, (DWORD)(offset >> 32), 1, 0)) {
				fioalkerr = (INT) GetLastError();
				if (fioalkerr != ERROR_LOCK_VIOLATION) return(ERR_LKERR);
				if (!timeout) return(ERR_NOACC);
				if (timeout > 0) {
					if (!time1) time1 = time(NULL) + timeout;
					else if (time(NULL) > time1) return(ERR_NOACC);
				}
				if (lockretrytime) Sleep(lockretrytime);
				continue;
			}
			break;
		}
	}
	else {
		if (!UnlockFile(handle, (DWORD) offset, (DWORD)(offset >> 32), 1, 0)) {
			fioalkerr = (INT) GetLastError();
			return(ERR_LKERR);
		}
	}
	return(0);
}

INT fioaflush(FHANDLE handle)
{
	if (!FlushFileBuffers(handle)) {
		fioaflerr = GetLastError();
		return(ERR_WRERR);
	}
	return(0);
}

INT fioatrunc(FHANDLE handle, OFFSET size)
{
	INT i1;

	if (size != -1L && (i1 = fioalseek(handle, size, 0, NULL))) return(i1);

	if (!SetEndOfFile(handle)) {
		fioatrerr = GetLastError();
		return(ERR_WRERR);
	}
	return(0);
}

INT fioadelete(TCHAR *filename)
{
	INT i1;
	TCHAR workname[MAX_NAMESIZE + 1];

	for (i1 = 0; filename[i1]; i1++) {
		if (filename[i1] == (TCHAR) '/') workname[i1] = (TCHAR) '\\';
		else workname[i1] = filename[i1];
	}
	workname[i1] = (TCHAR) '\0';

	if (!DeleteFile((LPCTSTR) workname)) {
		fioadlerr = GetLastError();
		return(ERR_DLERR);
	}
	return(0);
}

INT fioarename(TCHAR *oldname, TCHAR *newname)
{
	INT i1;
	TCHAR workname1[MAX_NAMESIZE + 1], workname2[MAX_NAMESIZE + 1];

	for (i1 = 0; oldname[i1]; i1++) {
		if (oldname[i1] == (TCHAR) '/') workname1[i1] = (TCHAR) '\\';
		else workname1[i1] = oldname[i1];
	}
	workname1[i1] = 0;
	for (i1 = 0; newname[i1]; i1++) {
		if (newname[i1] == (TCHAR) '/') workname2[i1] = (TCHAR) '\\';
		else workname2[i1] = newname[i1];
	}
	workname2[i1] = (TCHAR) '\0';

	if (_trename(workname1, workname2)) {
		if (errno == ENOENT) return ERR_FNOTF;
		if (errno == EACCES) return ERR_NOACC;
		return ERR_RENAM;
	}
	return 0;
}

INT fioafindfirst(TCHAR *path, TCHAR *file, TCHAR **found)
{
	INT i1;
	TCHAR workname[MAX_NAMESIZE + 1];

	for (i1 = 0; path[i1]; i1++) {
		if (path[i1] == (TCHAR) '/') workname[i1] = (TCHAR) '\\';
		else workname[i1] = path[i1];
	}
	if (i1 && workname[i1 - 1] != (TCHAR) '\\') workname[i1++] = (TCHAR) '\\';
	findpathlength = i1;
	_tcsncpy(foundfile, workname, i1);
	if (*file) {
		_tcscpy(&workname[i1], file);
		_tcscpy(findfile, file);
	}
	else {
		_tcscpy(&workname[i1], _T("*.*"));
		_tcscpy(findfile, _T("*"));
	}
	if (findhandle != INVALID_HANDLE_VALUE) FindClose(findhandle);
	findhandle = FindFirstFile(workname, &finddta);
	if (findhandle == INVALID_HANDLE_VALUE) return ERR_FNOTF;
	for ( ; ; ) {
		if (!(finddta.dwFileAttributes & (FILE_ATTRIBUTE_DIRECTORY | FILE_ATTRIBUTE_HIDDEN | FILE_ATTRIBUTE_SYSTEM | FILE_ATTRIBUTE_OFFLINE))
			&& finddta.cFileName[0] != (TCHAR) '.' && matchname(finddta.cFileName, findfile)) break;
		if (!FindNextFile(findhandle, &finddta)) {
			FindClose(findhandle);
			findhandle = INVALID_HANDLE_VALUE;
			return ERR_FNOTF;
		}
	}
	_tcscpy(foundfile + findpathlength, finddta.cFileName);
	*found = foundfile;
	return 0;
}

INT fioafindnext(TCHAR **found)
{
	if (findhandle == INVALID_HANDLE_VALUE) return ERR_NOTOP;

	for ( ; ; ) {
		if (!FindNextFile(findhandle, &finddta)) {
			FindClose(findhandle);
			findhandle = INVALID_HANDLE_VALUE;
			return ERR_FNOTF;
		}
		if (!(finddta.dwFileAttributes & (FILE_ATTRIBUTE_DIRECTORY | FILE_ATTRIBUTE_HIDDEN | FILE_ATTRIBUTE_SYSTEM | FILE_ATTRIBUTE_OFFLINE))
			&& finddta.cFileName[0] != (TCHAR) '.' && matchname(finddta.cFileName, findfile)) break;
	}
	_tcscpy(foundfile + findpathlength, finddta.cFileName);
	*found = foundfile;
	return 0;
}

INT fioafindclose()
{
	if (findhandle == INVALID_HANDLE_VALUE) return ERR_NOTOP;

	FindClose(findhandle);
	findhandle = INVALID_HANDLE_VALUE;
	return 0;
}

INT fioaslash(TCHAR *filename)
{
	INT i1;

	for (i1 = (INT)_tcslen(filename) - 1; i1 >= 0 && filename[i1] != (TCHAR) '\\' && filename[i1] != (TCHAR) '/'
			&& filename[i1] != (TCHAR) ':'; i1--);
	return(i1);
}

void fioaslashx(TCHAR *filename)
{
	size_t i1;

	i1 = _tcslen(filename);
	if (i1 && filename[i1 - 1] != (TCHAR) '\\' && filename[i1 - 1] != (TCHAR) '/' && filename[i1 - 1] != (TCHAR) ':') {
		filename[i1] = (TCHAR) '\\';
		filename[i1 + 1] = (TCHAR) '\0';
	}
}

static INT matchname(TCHAR *name, TCHAR *pattern)
{
	INT i1, i2;

	for (i1 = i2 = 0; pattern[i1]; i2++, i1++) {
		if (pattern[i1] == (TCHAR) '*') {
			do if (!pattern[++i1]) return TRUE;
			while (pattern[i1] == (TCHAR) '*');
			while (name[i2]) {
				if ((pattern[i1] == (TCHAR) '?' || pattern[i1] == name[i2]) && matchname(name + i2, pattern + i1)) return TRUE;
				i2++;
			}
			return FALSE;
		}
		if (pattern[i1] == (TCHAR) '?') {
			if (!name[i2]) return FALSE;
		}
		else {
			if (pattern[i1] == (TCHAR) '\\' && (pattern[i1 + 1] == (TCHAR) '\\' || pattern[i1 + 1] == (TCHAR) '*' || pattern[i1 + 1] == (TCHAR) '?')) i1++;
			if (_totlower(pattern[i1]) != _totlower(name[i2])) return FALSE;
		}
	}
	return !name[i2];
}
