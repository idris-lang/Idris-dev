# This makefile compiles the project 
#

.PHONY: all

sqltest : sqlite3.idr sqlite3api.o
	idris sqlite3.idr -o sqltest

sqlite3api.o : sqlite3api.c 
	gcc -c sqlite3api.c
             
all : sqltest sqlite3api.o
