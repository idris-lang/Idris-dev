/*
 *  sqlite3api.h
 *  
 *
 *  Created by Melissa Farinaz MOZIFIAN on 22/06/2012.
 *  Copyright 2012. All rights reserved.
 *
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sqlite3.h>
#include <ctype.h>
#include <gc.h>

typedef struct  {
	sqlite3 *db_ptr; // database pointer
	sqlite3_stmt *ppStmt; // statement pointer
	char buffer[1000]; // bufer to store errors returned by certain functions
	const char *Ptr_tail;
	sqlite3_value *value;
	int row_count; // row number store by exec function
	int col_count;
	
} DBinfo;

// struct used for backup functions
typedef struct {
	sqlite3 *source_ptr;
	sqlite3_backup *backup;
}DBbackup ;

// Table struct used by get_table function
// stores row and column
// returned by get_table
typedef struct {
	int num_row;
	int num_col;
	char** table_data;
	int data_size;
	int* data_type;
	DBinfo* database;
}Table;	


void* sqlite3_open_idr(const char *filename);

int exec_db(void*p);

int sqlite3_close_idr(void* db);

int sqlite3_exec_idr(void*, const char *sql);

char* sqlite3_get_error(void* db);

const unsigned char* sqlite3_get_val_text(void* p,int nCol);

void* sqlite3_get_table_idr(void* db, const char *sql);

void sqlite3_free_table_idr(void* db);

int sqlite3_get_num_col(void* p);

int sqlite3_get_num_row(void* p);

int sqlite3_get_num_row_v2(void* p);

int sqlite3_get_num_col_v2(void* p);

int sqlite3_get_data_type(void* p, int nRow, int nCol);

int sqlite3_get_val_int(void* p,int nCo);

float sqlite3_get_float(void* p, int nCol);

void* sqlite3_prepare_idr(
  void *db,            /* Database handle */
  const char *zSql    /* SQL statement, UTF-8 encoded */
);

int sqlite3_step_idr(void* stmt);

void* sqlite3_bind_float_idr(void* p,int index, float val);

void* sqlite3_bind_int_idr(void* p,int index , int val);

void* sqlite3_bind_null_idr(void* p,int index);

void* sqlite3_bind_text_idr(void* p,const char* text, int index,int length);

int sqlite3_column_count_idr(void* stmt, const char* tbl_name);

int sqlite3_data_count_idr(void* stmt);

int sqlite3_reset_idr(void* stmt);

int sqlite3_finalize_idr(void* stmt);

int sqlite3_complete_idr(const char *sql);

const char *sqlite3_column_decltype_idr(void* stmt,int n);

const char *sqlite3_column_name_idr(void* stmt, int N);

int sqlite3_column_bytes_idr(void* stmt, int n);

int sqlite3_column_bytes_idr(void* stmt, int n);

const void *sqlite3_column_blob_idr(void* stmt, int iCol);

const unsigned char *sqlite3_column_text_idr(void* stmt, int iCol);

int sqlite3_column_int_idr(void* stmt, int iCol);


void* sqlite3_backup_init_idr(void* pDestm,
							  const char *zDestName,
							  void* pSource,
							  const char *zSourceName
							  );

int sqlite3_backup_finish_idr(void *backup);

int sqlite3_backup_step_idr(void *backup, int nPage);

int sqlite3_backup_remaining_idr(void *backup);

int sqlite3_backup_pagecount_idr(void *backup);

int strLength(const char * str);
