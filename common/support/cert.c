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
 ******************************************************************************
 *
 *
 * openssl genrsa -out selfsigned.key 4096
 * openssl req -new -key selfsigned.key -out selfsigned.csr \
 *  -sha256 -subj "/C=US/ST=Wyoming/L=SelfSigned/O=Portable Software/OU=Org/CN=localhost"
 * openssl x509 -req -days 9000 -in selfsigned.csr -signkey selfsigned.key -out selfsigned.crt
 * cat selfsigned.crt selfsigned.key > dbcserver.crt
 *
 */
#include <openssl/bio.h>
#include <tchar.h>

#define INC_STRING 1
#include "includes.h"
#include "base.h"

static const TCHAR* defaultCertFileName = _T("dbcserver.crt");
static TCHAR certBioErrorMsg[300];
static const TCHAR* c1 = _T("-----BEGIN CERTIFICATE-----");
static const TCHAR* c2 = _T("-----END CERTIFICATE-----");
static const TCHAR* c3 = _T("-----BEGIN RSA PRIVATE KEY-----");
static const TCHAR* c4 = _T("-----END RSA PRIVATE KEY-----");
static BIO *memoryBio = NULL;
static TCHAR* buffer;
static FILE* crtfile;

/**
 * Called only from two places in clientstart() in dbcclnt.c
 * Only when this is a server
 */
BIO* GetCertBio(TCHAR* certificatefilename) {

	if (memoryBio == NULL) {
		certBioErrorMsg[0] = (TCHAR) '\0';
		if (certificatefilename == NULL || wcslen(certificatefilename) == 0) certificatefilename = (TCHAR*)defaultCertFileName;
		crtfile = _tfopen(certificatefilename, _T("rb"));
		if (crtfile == NULL) {
			_stprintf(certBioErrorMsg, _T("Failure opening certificate file. File name used='%s'"), certificatefilename);
			return NULL;
		}
		fseek(crtfile, 0, SEEK_END);
		size_t filesize = ftell(crtfile);
		if ((long int) filesize < 0) {
			_stprintf(certBioErrorMsg, _T("Failure getting size of certificate file. File name used='%s'"), certificatefilename);
			return NULL;
		}
		fseek(crtfile, 0, SEEK_SET);
		buffer = (TCHAR *) malloc(filesize + sizeof(TCHAR));
		if (buffer == NULL) {
			fclose(crtfile);
			_stprintf(certBioErrorMsg, _T("Failure getting certificate file '%s'. Unable to allocate memory for a read buffer"), certificatefilename);
			return NULL;
		}
		size_t i1 = fread(buffer, 1, filesize, crtfile);
		if (i1 != filesize) {
			free(buffer);
			_stprintf(certBioErrorMsg, _T("Failure reading certificate file. File name used='%s'"), certificatefilename);
			return NULL;
		}
		if (filesize < 150) {
			_stprintf(certBioErrorMsg, _T("Failure in the certificate file '%s'. It is mal-formed"), certificatefilename);
			return NULL;
		}
		if (_tcsstr((const TCHAR *)(buffer), c1) == NULL || _tcsstr((const TCHAR *)(buffer), c2) == NULL) {
			_stprintf(certBioErrorMsg, _T("Failure in the certificate file '%s'. It is missing the certificate"), certificatefilename);
			return NULL;
		}
		if (_tcsstr((const TCHAR *)(buffer), c3) == NULL || _tcsstr((const TCHAR *)(buffer), c4) == NULL) {
			_stprintf(certBioErrorMsg, _T("Failure in the certificate file '%s'. It is missing the key"), certificatefilename);
			return NULL;
		}
		// The below call creates a read-only memory BIO
		memoryBio = BIO_new_mem_buf(buffer, (int)filesize);
		fclose(crtfile);
	}
	else BIO_reset(memoryBio);
	return memoryBio;
}

void FreeCertBio() {
	if (memoryBio != NULL) {
		BIO_vfree(memoryBio);
		free(buffer);
		memoryBio = NULL;
		buffer = NULL;
	}
}

TCHAR* GetCertBioErrorMsg() {
	return certBioErrorMsg;
}
