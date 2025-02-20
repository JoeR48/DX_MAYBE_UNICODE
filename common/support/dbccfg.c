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
#define INC_STDLIB
#define INC_STRING
#define INC_CTYPE

#include "includes.h"
#include "release.h"
#include "base.h"
#include "dbccfg.h"
#include "xml.h"
#include "fio.h"

#if OS_WIN32
#include <tchar.h>
#include <wchar.h>
#endif

static ELEMENT *getxmldata(TCHAR *, INT);
static ELEMENT *getnonxmldata(TCHAR *);
static INT processcfgentry(ELEMENT *, TCHAR *);
static INT buildxmlentry(TCHAR *, ELEMENT *, INT);
static void cfgseterror(TCHAR *);

static INT FLAG_NONE  = 0x000;
static INT FLAG_DIR   = 0x001;
static INT FLAG_PROG  = 0x002;

static ELEMENT *xmlbuffer;
static INT initflag = FALSE;
static TCHAR cfgerrorstring[CFG_MAX_ERRMSGSIZE];
static TCHAR key[CFG_MAX_KEYDEPTH][CFG_MAX_KEYLENGTH];
	
#define REQUIRES_DIR(a, b, c, d) ( \
	(!_tcscmp(a, _T("file")) && !_tcscmp(b, _T("dbc"))) || \
	(!_tcscmp(a, _T("file")) && !_tcscmp(b, _T("editcfg"))) || \
	(!_tcscmp(a, _T("file")) && !_tcscmp(b, _T("image"))) || \
	(!_tcscmp(a, _T("file")) && !_tcscmp(b, _T("open"))) || \
	(!_tcscmp(a, _T("file")) && !_tcscmp(b, _T("prep"))) || \
	(!_tcscmp(a, _T("file")) && !_tcscmp(b, _T("prt"))) || \
	(!_tcscmp(a, _T("file")) && !_tcscmp(b, _T("source"))) || \
	(!_tcscmp(a, _T("file")) && !_tcscmp(b, _T("fonts"))) || \
	(!_tcscmp(a, _T("file")) && !_tcscmp(b, _T("tdf"))) || \
	(!_tcscmp(a, _T("file")) && !_tcscmp(b, _T("tdb"))) || \
	(!_tcscmp(a, _T("file")) && !_tcscmp(b, _T("volume"))) \
)

#define REQUIRES_PROG(a, b, c, d) ( \
	(!_tcscmp(a, _T("stop"))) || \
	(!_tcscmp(a, _T("start"))) || \
	(!_tcscmp(a, _T("preload"))) \
)

#if OS_WIN32
#define ERRORVALUE() GetLastError()
#else
#include <errno.h>
#define ERRORVALUE() errno
#endif

/**
 * cfginit
 *
 * Reads configuration file from disk and calls appropriate routine to parse the
 * file and generate XML string.  Returns 0 on success, any other value returned
 * indicates that an error occurred.  Call cfggeterror() to return the error 
 * message. 
 *
 */
INT cfginit(TCHAR *cfgfile, INT required)
{
	INT i1, i2, filesize;
	TCHAR *filebuffer, *ptr, work[256];
	FILE *file; // @suppress("Statement has no effect")
	ELEMENT *element;
	ATTRIBUTE *attribute;

#if defined(FS_MAJOR_VERSION)
	ELEMENT *child;
#endif

	if (initflag) return 0;
	if (cfgfile == NULL) {
		/* NOTE: This isn't being used for anything as far as I know */
		filesize = 11;
		filebuffer = (TCHAR *) malloc((filesize + 1) * sizeof(TCHAR));
		if (filebuffer == NULL) {
			cfgseterror(_T("configuration file error: insufficient memory"));
			return RC_ERROR;
		}
		_stprintf(filebuffer, _T("<%scfg/>"), CFG_PREFIX);
	}
	else {
		i2 = FALSE;
		if (cfgfile[0]) ptr = cfgfile;
		else if (miogetenv(_T("DBC_CFG"), &ptr) || !*ptr) {
#if OS_WIN32
			_stprintf(cfgfile, _T(".\\%s.cfg"), CFG_PREFIX);
#else
			_stprintf(cfgfile, _T("./%s.cfg"), CFG_PREFIX);
#endif
			ptr = cfgfile;
			i2 = TRUE;
		}
		file = _tfopen(ptr, _T("rb"));
		if (file == NULL) {
			if (i2 && !required) {
				/* this code allows utilities to work when config was not specified */
				filesize = 11;
				filebuffer = (TCHAR *) malloc((filesize + 1) * sizeof(TCHAR));
				if (filebuffer == NULL) {
					cfgseterror(_T("configuration file error: insufficient memory"));
					return -1;
				}
				_stprintf(filebuffer, _T("<%scfg/>") CFG_PREFIX);			
			}
			else {
				_stprintf(work, _T("configuration file error: file open failed, err=%d"), (INT)ERRORVALUE());
				cfgseterror(work);
				return RC_ERROR;
			}
		}
		else {
			fseek(file, 0, 2);
			filesize = (INT) ftell(file);
			fseek(file, 0, 0);
			filebuffer = (TCHAR *) malloc((filesize + 1) * sizeof(TCHAR));
			if (filebuffer == NULL) {
				fclose(file);
				cfgseterror(_T("configuration file error: insufficient memory"));
				return -1;
			}
			i1 = (INT)fread(filebuffer, 1, filesize, file);
			fclose(file);
			if (i1 != filesize) {
				free(filebuffer);
				cfgseterror(_T("configuration file error: reading configuration file failed"));
				return RC_ERROR;
			}
			filebuffer[i1] = '\0';
		}
	}
	for (i1 = 0;
			i1 < filesize && (_istspace((int)filebuffer[i1]) || filebuffer[i1] == '\n' || filebuffer[i1] == '\r');
			i1++);
	if (i1 < filesize && filebuffer[i1] == '<') {
		xmlbuffer = getxmldata(filebuffer + i1, filesize - i1);
		free(filebuffer);
		if (xmlbuffer == NULL) {
			return RC_ERROR;
		}
		_stprintf(work, _T("%scfg"), CFG_PREFIX);
		for (element = xmlbuffer; element != NULL && (element->cdataflag || _tcscmp(element->tag, work)); element = element->nextelement);
		if (element == NULL) {
			free(xmlbuffer);
			_stprintf(work,  _T("configuration file error: '%scfg' element missing"), CFG_PREFIX);
			cfgseterror(work);
			return RC_ERROR;
		}
#if defined(FS_MAJOR_VERSION)
	 	/* create non-existent <file> element and insert it */	
	 	child = (ELEMENT *) malloc(sizeof(ELEMENT));
		if (child == NULL) {
			cfgseterror(_T("configuration file error: insufficient memory"));
			return RC_ERROR;
		}
		child->tag = (TCHAR *) malloc(sizeof(TCHAR) * 5);
		if (child->tag == NULL) {
			cfgseterror(_T("configuration file error: insufficient memory"));
			return RC_ERROR;
		}
		_tcscpy(child->tag, _T("file"));
		child->cdataflag = 0;
		child->firstattribute = NULL;	
		child->nextelement = NULL;		
		child->firstsubelement = element->firstsubelement;
		element->firstsubelement = child;		
		/* do conversions from fs tags to dx tags */
		for (element = child->firstsubelement; element != NULL; element = element->nextelement) {
			if (!_tcscmp(element->tag, _T("filepath"))) _tcscpy(element->tag, _T("open"));
			else if (!_tcscmp(element->tag, _T("preppath"))) _tcscpy(element->tag, _T("prep"));
			else if (!_tcscmp(element->tag, _T("nodigitcompression") || !_tcscmp(element->tag, _T("noexclusivesupport"))) {
				if (!_tcscmp(element->tag, _T("nodigitcompression"))) _tcscpy(element->tag, _T("ichrs"));
				else _tcscpy(element->tag, _T("exclusive"));
				child = (ELEMENT *) malloc(sizeof(ELEMENT));
				if (child == NULL) {
					cfgseterror(_T("configuration file error: insufficient memory"));
					return RC_ERROR;
				}
				if (!_tcscmp(element->tag, _T("ichrs")) child->cdataflag = 2;
				else child->cdataflag = 3;
				child->tag = (TCHAR *) malloc(sizeof(TCHAR) * 4);
				if (child->tag == NULL) {
					cfgseterror(_T("configuration file error: insufficient memory"));
					return RC_ERROR;
				}
				if (!_tcscmp(element->tag, "ichrs")) _tcscpy(child->tag, "on");
				else _tcscpy(child->tag, "off");
				child->firstsubelement = NULL;
				child->firstattribute = NULL;	
				child->nextelement = NULL;
				element->firstsubelement = child;	
			}
		}
#endif		
	}
	else {
		xmlbuffer = getnonxmldata(filebuffer + i1);
		free(filebuffer);
		if (xmlbuffer == NULL) {
			return RC_ERROR;
		}
		/* indicate that tree is minimal - that there are no duplicate entries at each level */
		attribute = (ATTRIBUTE *) malloc(sizeof(ATTRIBUTE));
		if (attribute == NULL) {
			cfgseterror(_T("configuration file error: insufficient memory"));
			return RC_ERROR;
		}
		attribute->nextattribute = NULL;
		attribute->tag = (TCHAR *) malloc(sizeof(TCHAR) * 8);
		if (attribute->tag == NULL) {
			free(attribute);
			cfgseterror(_T("configuration file error: insufficient memory"));
			return RC_ERROR;
		}
		attribute->cbTag = sizeof(TCHAR) * 8;
		_tcscpy(attribute->tag,  _T("reduced"));
		attribute->value = (TCHAR *) malloc(sizeof(TCHAR) * 2);
		if (attribute->value == NULL) {
			free(attribute);
			cfgseterror(_T("configuration file error: insufficient memory"));
			return RC_ERROR;
		}
		_tcscpy(attribute->value, _T("y"));
		xmlbuffer->firstattribute = attribute;
	}
	initflag = TRUE;
	return 0;
}

/**
 * getnonxmldata
 *
 * Preprocess configuration settings in non-xml configuration file.  Returns
 * NULL on error, otherwise a valid pointer to the root xml element is
 * returned.  Call cfggeterror() to return the error message. 
 *
 */
static ELEMENT *getnonxmldata(TCHAR *filebuffer) 
{
	INT i1, i2, state, kvsize;
	TCHAR kvpair[CFG_MAX_ENTRYSIZE], buffer[CFG_MAX_ENTRYSIZE], *ptr;
	ELEMENT *root;

	root = (ELEMENT *) malloc(sizeof(ELEMENT));
	if (root == NULL) {
		cfgseterror(_T("configuration file error: insufficient memory"));
		return NULL;
	}
	memset(root, 0, sizeof(ELEMENT));
	root->tag = (TCHAR *) malloc(sizeof(TCHAR) * 9); /* extra 3 bytes are for 'c' 'f' 'g' later */
	if (root->tag == NULL) {
		cfgseterror(_T("configuration file error: insufficient memory"));
		return NULL;
	}
	_tcscpy(root->tag, CFG_PREFIX);
	for (state = 1, kvsize = 0, ptr = filebuffer;;) {
		if (!*ptr) break;
		i1 = 0;
		while (*ptr) {
			if (*ptr == '\n') {
				ptr++;
				break;
			}
			buffer[i1++] = *ptr++;
		}
		buffer[i1] = '\0';
		i1 = (INT)_tcslen(buffer);
		if (i1 && buffer[i1 - 1] == '\r') i1--;
		while (i1 >= 1 && _istspace((int)buffer[i1 - 1])) {
			if (i1 >= 2 && buffer[i1 - 2] == '\\') {
				for (i2 = 1; i1 >= i2 + 2 && buffer[i1 - (i2 + 2)] == '\\'; i2++);
				if (i2 & 0x01) break;
			}
			i1--;
		}
		buffer[i1] = '\0';
		for (i1 = 0; buffer[i1] && _istspace((int)buffer[i1]); i1++);
		if (state != 4) {
			if (!isalpha((int)buffer[i1])) continue;
#if defined(DX_MAJOR_VERSION)	
			for (i2 = 0; root->tag[i2] && root->tag[i2] == buffer[i1 + i2]; i2++);
			if (root->tag[i2] || buffer[i1 + i2] != '.') continue;
#endif
		}
		do {
			/* remove spaces before '=' */
			if (_istspace((int)buffer[i1])) {
				if (state < 3) continue; 
			}
			else if (state == 1 && buffer[i1] == '=') {
				state = 2;
			}
			else if (state == 2) state = 3;
#if defined(DX_MAJOR_VERSION)			
			/* remove slash and check for line continuation */
			if (state >= 3 && buffer[i1] == '\\') { 
				if (!buffer[++i1]) {
					state = 4;
					break;
				}
			}
#endif			
			kvpair[kvsize++] = buffer[i1];
		} while (buffer[++i1]);
		if (state != 4) {
			state = 1;
			kvpair[kvsize++] = '\0';
			kvsize = 0; /* reset */
			if (processcfgentry(root, kvpair) < 0) {
				return NULL;	
			}
		}		
		
	}
	_tcscat(root->tag, _T("cfg"));
	return root;
}

/**
 * processcfgentry
 *
 */
static INT processcfgentry(ELEMENT *root, TCHAR *kvpair) {
	INT i1, i2, keynum;
	key[0][0] = key[1][0] = key[2][0] = key[3][0] = '\0';
#if defined(FS_MAJOR_VERSION) /** FS CONVERSIONS **/
	if (!_tcscmp(kvpair, "noexclusivesupport")) _tcscpy(kvpair, "exclusive=off"); /* fs conversion */
	if (!_tcscmp(kvpair, "nodigitcompression")) _tcscpy(kvpair, "ichrs=off"); /* fs conversion */
	memmove(kvpair + 11, kvpair, _tcslen(kvpair) + 1); 
	memcpy(kvpair, "dbcfs.file.", 11);
#endif	

	for (i1 = i2 = keynum = 0; kvpair[i1]; i1++) {
		if (kvpair[i1] == '.' || kvpair[i1] == '=') {
			if (keynum > 0) key[keynum - 1][i2] = '\0';
			if (kvpair[i1] == '=') {
				i1++;
				break;
			}
			i2 = 0;
			keynum++;
			continue;
		}
		if (keynum > 0) key[keynum - 1][i2] = kvpair[i1]; 
		i2++;
	}
	/*
	 * if (!key[0]) return 0;
	 * The above never happened because the boolean would always be false as key[0] is an address
	 * and is therefor always true.
	 */
#if defined(DX_MAJOR_VERSION) /** DX CONVERSIONS **/
	if (keynum == 4 && !_tcscmp(key[3], _T("server"))) {
		/* make adjustment for dbcdx.file.server.fsname.server to keep XML correct */
		_tcscpy(key[3], _T("serverhost"));
	}
	if (keynum == 3 && !_tcscmp(key[1], _T("vol"))) {
		/* convert to FS style volume */
		_tcscpy(key[1], _T("volume"));
		i2 = (INT)_tcslen(key[2]);
		kvpair[(i1 - i2) - 2] = '=';
		kvpair[i1 - 1] = ' ';
		key[2][0] = '\0';
		i1 -= (i2 + 1);
	}
#endif
#if defined(FS_MAJOR_VERSION) /** FS CONVERSIONS **/
	if (!_tcscmp(key[1], "collatemap")) _tcscpy(key[1], "collate");
	else if (!_tcscmp(key[1], "filepath")) _tcscpy(key[1], "open");
	else if (!_tcscmp(key[1], "preppath")) _tcscpy(key[1], "prep");
#endif	
	if (buildxmlentry(kvpair + i1, root, 0) < 0) {
		return RC_ERROR;
	}
	return 0;
}

/**
 * buildxmlentry
 *
 */
static INT buildxmlentry(TCHAR *value, ELEMENT *ptr, INT level) {
	INT i1, i2, flag;
	TCHAR *p1;
	ELEMENT *e1, *child, *parent;
	
/** CODE: SORT ENTRIES IN TREE THEN ADD SORTED="Y" ATTRIBUTE TO ROOT **/	
	parent = ptr;
	ptr = ptr->firstsubelement;
	while (ptr != NULL) {
		if (!_tcscmp(ptr->tag, key[level]) && !(level == 1 && !_tcscmp(key[0], _T("file")) && !_tcscmp(key[1], _T("volume")))
				 && !(level == 2 && !_tcscmp(key[0], _T("file")) && !_tcscmp(key[1], _T("prefix"))))
		{
			/* found match */	
			return buildxmlentry(value, ptr, level + 1);
		}
		ptr = ptr->nextelement;
	}
	if (ptr == NULL) {
		while (level < CFG_MAX_KEYDEPTH && key[level][0]) {
			/* no match, normal insert */
			child = (ELEMENT *) malloc(sizeof(ELEMENT));
			if (child == NULL) {
				cfgseterror(_T("configuration file error: insufficient memory"));
				return RC_ERROR;
			}
			child->tag = (TCHAR *) malloc(sizeof(TCHAR) * (_tcslen(key[level]) + 1));
			if (child->tag == NULL) {
				cfgseterror(_T("configuration file error: insufficient memory"));
				return RC_ERROR;
			}
			_tcscpy(child->tag, key[level]);
			child->cdataflag = 0;
			child->firstsubelement = NULL;
			child->firstattribute = NULL;	
			child->nextelement = parent->firstsubelement;
			parent->firstsubelement = child;
			level++;
			parent = child;
		}
		if (REQUIRES_DIR(key[0], key[1], key[2], key[3])) flag = FLAG_DIR;
		else if (REQUIRES_PROG(key[0], key[1], key[2], key[3])) flag = FLAG_PROG;
		else flag = FLAG_NONE;
		if (flag != FLAG_NONE) {
			if (!_tcscmp(key[0], _T("file")) && !_tcscmp(key[1], _T("volume"))) {
				/* split of volume name and directory, create xml elements */
				p1 = value;
				while (*p1 == ' ' || *p1 == '\t') p1++;
				
				for (i1 = 0, i2 = (INT)_tcslen(p1); i1 < i2; i1++) {
					if (p1[i1] == ' ') {
						p1[i1] = '\0';
						break;
					}
				}
				if (i1 == i2) {
					cfgseterror(_T("configuration file error: invalid volume specification"));
					return RC_ERROR;
				}

				child = (ELEMENT *) malloc(sizeof(ELEMENT));
				if (child == NULL) {
					cfgseterror(_T("configuration file error: insufficient memory"));
					return RC_ERROR;
				}
				child->tag = (TCHAR *) malloc(sizeof(TCHAR) * 5);
				if (child->tag == NULL) {
					free(child);
					cfgseterror(_T("configuration file error: insufficient memory"));
					return RC_ERROR;
				}
				_tcscpy(child->tag, _T("name"));
				child->cdataflag = 0;
				child->firstsubelement = NULL;
				child->firstattribute = NULL;	
				child->nextelement = NULL;
				parent->firstsubelement = child;
				
				e1 = (ELEMENT *) malloc(sizeof(ELEMENT));
				if (e1 == NULL) {
					cfgseterror(_T("configuration file error: insufficient memory"));
					return RC_ERROR;
				}
				e1->cdataflag = (INT)_tcslen(p1);
				e1->tag = (TCHAR *) malloc(sizeof(TCHAR) * (_tcslen(p1) + 1));
				if (e1->tag == NULL) {
					free(e1);
					cfgseterror(_T("configuration file error: insufficient memory"));
					return RC_ERROR;
				}
				_tcscpy(e1->tag, p1);
				e1->firstsubelement = NULL;
				e1->firstattribute = NULL;	
				e1->nextelement = NULL;
				child->firstsubelement = e1;
				
				value += ++i1; /* value now points at directory list */
			}
			/* break down semicolon delimited list of values into children */
			for (i1 = 0, p1 = value, i2 = (INT)_tcslen(p1); i1 < i2; i1++) {
				if (value[i1] == ';' || (i1 + 1) == i2) {	
					if (value[i1] == ';') value[i1] = '\0';		
					child = (ELEMENT *) malloc(sizeof(ELEMENT));
					if (child == NULL) {
						cfgseterror(_T("configuration file error: insufficient memory"));
						return RC_ERROR;
					}
					if (flag == FLAG_DIR) {
						child->tag = (TCHAR *) malloc(sizeof(TCHAR) * 4);
						if (child->tag == NULL) {
							free(child);
							cfgseterror(_T("configuration file error: insufficient memory"));
							return RC_ERROR;
						}
						_tcscpy(child->tag, _T("dir"));
					}
					else if (flag == FLAG_PROG) {
						child->tag = (TCHAR *) malloc(sizeof(TCHAR) * 5);
						if (child->tag == NULL) {
							free(child);
							cfgseterror(_T("configuration file error: insufficient memory"));
							return RC_ERROR;
						}
						_tcscpy(child->tag, _T("prog"));
					}

					child->cdataflag = 0;
					child->firstsubelement = NULL;
					child->firstattribute = NULL;	
					child->nextelement = NULL;
					if (parent->firstsubelement == NULL) parent->firstsubelement = child;
					else {
						e1 = parent->firstsubelement;
						while (e1 != NULL) {
							if (e1->nextelement == NULL) break;
							e1 = e1->nextelement;
						}
						e1->nextelement = child;
					}
					e1 = (ELEMENT *) malloc(sizeof(ELEMENT));
					if (e1 == NULL) {
						cfgseterror(_T("configuration file error: insufficient memory"));
						return RC_ERROR;
					}
					e1->cdataflag = (INT)_tcslen(p1);
					e1->tag = (TCHAR *) malloc(sizeof(TCHAR) * (_tcslen(p1) + 1));
					if (e1->tag == NULL) {
						free(e1);
						cfgseterror(_T("configuration file error: insufficient memory"));
						return RC_ERROR;
					}
					_tcscpy(e1->tag, p1);
					e1->firstsubelement = NULL;
					e1->firstattribute = NULL;	
					e1->nextelement = NULL;
					child->firstsubelement = e1;
					p1 = value + i1 + 1;			
				}
			}
		}
		else {
			if (_tcslen(value) == 0) {
				child = NULL;
			}
			else {
				child = (ELEMENT *) malloc(sizeof(ELEMENT));
				if (child == NULL) {
					cfgseterror(_T("configuration file error: insufficient memory"));
					return RC_ERROR;
				}
				child->cdataflag = (INT)_tcslen(value);
				child->tag = (TCHAR *) malloc(sizeof(TCHAR) * (child->cdataflag + 1));
				if (child->tag == NULL) {
					cfgseterror(_T("configuration file error: insufficient memory"));
					return RC_ERROR;
				}
				_tcscpy(child->tag, value);
				child->firstsubelement = NULL;
				child->firstattribute = NULL;	
				child->nextelement = NULL;
			}
			parent->firstsubelement = child;
		}
	}
	return 0;
}

/**
 * getxmldata
 *
 * Processes a configuration file that contains xml configuration options.
 * Returns NULL on error, otherwise a valid pointer to the root xml element 
 * is returned.  Call cfggeterror() to return the error message. 
 *
 */
static ELEMENT *getxmldata(TCHAR *filebuffer, INT filesize)
{
	INT i1, i2, i3;
	TCHAR error[CFG_MAX_ERRMSGSIZE], *ptr;
	ELEMENT *xmlbuffer_p;

	for (i1 = i2 = i3 = 0; i1 < filesize; ) {
		for ( ; i1 < filesize && filebuffer[i1] != '\n' && filebuffer[i1] != '\r' && (UCHAR) filebuffer[i1] != DBCEOR && (UCHAR) filebuffer[i1] != DBCEOF; i1++) {
			if (filebuffer[i1] == '<' && i1 + 1 < filesize && (filebuffer[i1 + 1] == '!' || filebuffer[i1 + 1] == '?')) {
				/* comment or meta data */
				if (filebuffer[++i1] == '!') {  /* <!-- anything --> */
					for (i1++; i1 + 2 < filesize && (filebuffer[i1] != '-' || filebuffer[i1 + 1] != '-' || filebuffer[i1 + 2] != '>'); i1++);
					if ((i1 += 2) >= filesize) { /* invalid comment */
						cfgseterror(_T("CFG contains invalid XML comment"));
						return NULL;
					}
				}
				else {  /* <?tagname [attribute="value" ...] ?> */
					for (i1++; i1 + 1 < filesize && (filebuffer[i1] != '?' || filebuffer[i1 + 1] != '>'); i1++);
					if (++i1 >= filesize) { /* invalid meta data */
						cfgseterror(_T("CFG contains invalid XML meta data"));
						return NULL;
					}
				}
				continue;
			}
			filebuffer[i2++] = filebuffer[i1];
			if (!_istspace((int)filebuffer[i1])) i3 = i2;
		}
		for (i2 = i3;
				i1 < filesize
				&& (_istspace((int)filebuffer[i1]) || filebuffer[i1] == '\n' || filebuffer[i1] == '\r'
						|| (UCHAR) filebuffer[i1] == DBCEOR || (UCHAR) filebuffer[i1] == DBCEOF); i1++);
	}
	for (i3 = 512; i3 < i2; i3 <<= 1);
	xmlbuffer_p = (ELEMENT *) malloc(i3);
	if (xmlbuffer_p == NULL) {
		cfgseterror(_T("configuration file error: insufficient memory"));
		return NULL;
	}
	while ((i1 = xmlparse(filebuffer, i2, xmlbuffer_p, i3)) == -1) {
		ptr = (TCHAR *) realloc(xmlbuffer_p, i3 << 1);
		if (ptr == NULL) {
			free(xmlbuffer_p);
			cfgseterror(_T("configuration file error: insufficient memory"));
			return NULL;
		}
		xmlbuffer_p = (ELEMENT *) ptr;
		i3 <<= 1;
	}
	if (i1 < 0) {
		free(xmlbuffer_p);
		_tcscpy(error, _T("configuration file error: file contains invalid XML format: "));
		_tcscat(error, xmlgeterror());
		cfgseterror(error);
		return NULL;
	}
	return xmlbuffer_p;
}

/**
 * cfgseterror()
 *
 * Set error message.
 *
 */
static void cfgseterror(TCHAR *error) {
	_tcscpy(cfgerrorstring, error);
}

/**
 * cfggeterror()
 *
 * Return last error message.
 *
 */
TCHAR * cfggeterror()
{
	return cfgerrorstring;
}

ELEMENT * cfggetxml()
{
	return xmlbuffer;
}

/**
 * cfgexit()
 *
 * Free resources if necessary.  Should be called when DB/C terminates.
 *
 */
void cfgexit() 
{
	if (!initflag) return;
	cfgerrorstring[0] = '\0';
	free(xmlbuffer);
}
