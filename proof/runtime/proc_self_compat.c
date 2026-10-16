#define _GNU_SOURCE
#include <dlfcn.h>
#include <sys/auxv.h>
#include <unistd.h>
#include <string.h>
#include <stdlib.h>
#include <limits.h>
#include <stdio.h>
ssize_t readlink(const char *path, char *buf, size_t size) {
 static ssize_t (*original)(const char*,char*,size_t);
 if (!original) original=dlsym(RTLD_NEXT,"readlink");
 if ((strcmp(path,"/proc/self/exe")==0 || (strncmp(path,"/proc/",6)==0 && atoi(path+6)==getpid() && strstr(path,"/exe")!=NULL))) {
  const char *exec=(const char*)getauxval(AT_EXECFN);char resolved[PATH_MAX];
  if (exec && realpath(exec,resolved)) {size_t n=strlen(resolved); if(n>size)n=size; memcpy(buf,resolved,n); return n;}
 }
 return original(path,buf,size);
}
char *realpath(const char *path, char *resolved) {
 static char *(*original)(const char*,char*);
 if (!original) original=dlsym(RTLD_NEXT,"realpath");
 if ((strcmp(path,"/proc/self/exe")==0 || (strncmp(path,"/proc/",6)==0 && atoi(path+6)==getpid() && strstr(path,"/exe")!=NULL))) {
  const char *exec=(const char*)getauxval(AT_EXECFN);
  if(exec) return original(exec,resolved);
 }
 return original(path,resolved);
}
char *__realpath_chk(const char *path,char *resolved,size_t size) {return realpath(path,resolved);}
