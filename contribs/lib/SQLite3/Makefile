# This makefile compiles the project 
#

.PHONY: all

sqltest : testunit.idr Sqlite3.idr sqlite3api.o
	idris testunit.idr -o sqltest

sqlite3api.o : sqlite3api.c 
	gcc -c sqlite3api.c
             
all : sqltest sqlite3api.o

