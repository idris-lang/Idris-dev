/*
 *  sqlite3api.c
 *  
 *
 *  Created by Melissa Farinaz MOZIFIAN on 22/06/2012.
 *  Copyright 2012. All rights reserved.
 *
 */


#include "sqlite3api.h"



static char sql_query_buffer[2000];
unsigned char* array;

void* sqlite3_open_idr(const char *filename){
	
	sqlite3 *db;
	int res =sqlite3_open(filename,&db);
	
	if(res != SQLITE_OK){
		printf("Error occured while opening the databse.");
		return NULL;
	}
	DBinfo *dbi = malloc(sizeof(DBinfo));
	dbi->db_ptr = db;
	return dbi;
	
}

int sqlite3_close_idr(void* db){
	
	DBinfo* dbi =(DBinfo*) db;
	int res =sqlite3_close(dbi->db_ptr);
	if (res == SQLITE_OK){
		free(dbi);
		printf("Successfuly closed the databse\n");
		return 0;
	}
	
	if(res == SQLITE_BUSY){
		printf("SQL Busy");
		return 5;
	}
	
	else {
		return 1;
	}	
}

int sqlite3_exec_idr(void* db, const char *sql)
{
	
	DBinfo* dbi =(DBinfo*) db;
	char* err;
	int rc;
	
	rc = sqlite3_exec(dbi->db_ptr,sql,NULL, NULL, &err);
	printf("%d\n", rc);
	if (rc != SQLITE_OK && err != NULL) {
		strncpy(dbi->buffer, err, sizeof(dbi->buffer));
		sqlite3_free(err);
	}
	return rc;
}


char* sqlite3_get_error(void* db) {
	DBinfo* dbi =(DBinfo*) db;
	return dbi->buffer;
}

void* sqlite3_prepare_idr(void *db,const char *zSql){
	
	sqlite3_stmt* stmt;
	const char *tail;
	
	DBinfo* dbi =(DBinfo*) db;
	
	int rec = sqlite3_prepare_v2(dbi->db_ptr,zSql,-1,&stmt,&tail);
	dbi ->ppStmt =stmt;
	dbi ->Ptr_tail = tail;
	
	if(rec != SQLITE_OK){
		return NULL;
	}
	
	return dbi;
}

void* sqlite3_get_table_idr(void* db,
							const char *sql){
	
	DBinfo* dbi =(DBinfo*) db;
	char* err;

	Table* tbl = malloc(sizeof(Table));
	tbl->database = dbi;
	
	int res = sqlite3_get_table(dbi->db_ptr,sql,&tbl->table_data,&tbl->num_row,&tbl->num_col,&err);
	
	int array_size = sizeof(&tbl->table_data);

	if( res != SQLITE_OK && err != NULL){
		strncpy(dbi->buffer, err, sizeof(dbi->buffer));
		sqlite3_free(err);
		return NULL;
	}
	
	tbl -> data_size = array_size;
	return tbl;
	
}

int exec_db(void*p){
	
	DBinfo* dbi =(DBinfo*) p;
	int rc, col, row_counter;
	
	const char* col_name;
	
	rc = sqlite3_step(dbi->ppStmt);

	if( rc == SQLITE_DONE){
		return rc;
	}
	if(rc == SQLITE_ERROR && rc == SQLITE_MISUSE){
		return 1;
	}

	row_counter =0;
	
	while (rc == SQLITE_ROW) {
		
		rc = sqlite3_step(dbi->ppStmt);
		row_counter++;
	}
	
	col = sqlite3_column_count(dbi->ppStmt);
	dbi->row_count = row_counter;
	dbi->col_count = col;
	return rc;
	
}

int sqlite3_get_num_row_v2(void* p){
	
	DBinfo* dbi =(DBinfo*) p;
	int row_number =dbi->row_count;
	return row_number;
	
	
}

int sqlite3_get_num_col_v2(void* p){
	
	DBinfo* dbi =(DBinfo*) p;
	int col_number =dbi-> col_count;
	return col_number;
	
}


int sqlite3_get_num_row(void* p){
	
	Table* tbl =(Table*) p;
	int row_number =tbl->num_row;
	return row_number;
	
	
}

int sqlite3_get_num_col(void* p){
	
	Table* tbl =(Table*) p;
	int col_number =tbl-> num_col;
	return col_number;
	
}
int sqlite3_get_data_type_v2(void* p, int nRow, int nCol){
	
	DBinfo* dbi =(DBinfo*) p;
	int rc, type, row_counter;
	const char* char_int;

	rc = sqlite3_reset(dbi->ppStmt);
	rc = sqlite3_step(dbi->ppStmt);
	row_counter =0;
	
	while (rc == SQLITE_ROW && row_counter < nRow) {
		
		rc = sqlite3_step(dbi->ppStmt);
		row_counter++;
	}
	type =sqlite3_column_type(dbi->ppStmt, nCol);
	return  type;
	
}


int sqlite3_get_val_int_v2(void* p, int nCol){
	
	
	DBinfo* dbi =(DBinfo*) p;
	int val, col;
	
	val =sqlite3_column_int(dbi->ppStmt, nCol);
	return  val;
	
	
}

int sqlite3_get_data_type(void* p,const char* tbl_name, int nRow, int nCol){
	
	DBinfo* dbi =(DBinfo*) p;
	sqlite3_stmt* stmt;
	const char *tail;
	int rc,i, val, counter;
	const char* char_int;
	
	counter =0;
	strcpy(sql_query_buffer, "select * from ");
	strcat(sql_query_buffer, tbl_name);
	
	rc = sqlite3_prepare_v2(dbi->db_ptr, sql_query_buffer, -1, &stmt, &tail);
	if(rc != SQLITE_OK){
		fprintf(stderr, "SQL Prepare error\n");
		return rc;
	}
	rc = sqlite3_step(stmt);
	
	while (rc == SQLITE_ROW && counter < nRow){
		
		rc = sqlite3_step(stmt);
		counter++;
		
	}
	
	val =sqlite3_column_type(stmt, nCol);
	
	rc =sqlite3_finalize(stmt);
	if( rc != SQLITE_OK){
		printf("Couldnt finalize:\n");
	}
	return  val;
	
}


int sqlite3_get_val_int(void* p,const char* tbl_name, int nRow, int nCol){
	
	
	DBinfo* dbi =(DBinfo*) p;
	sqlite3_stmt* stmt;
	const char *tail;
	int rc,i, val, counter;
	const char* char_int;
	
	counter =0;
	strcpy(sql_query_buffer, "select * from ");
	strcat(sql_query_buffer, tbl_name);
	
	rc = sqlite3_prepare_v2(dbi->db_ptr, sql_query_buffer, -1, &stmt, &tail);
	if(rc != SQLITE_OK){
		fprintf(stderr, "SQL Prepare error\n");
		return rc;
	}
	rc = sqlite3_step(stmt);

	while (rc == SQLITE_ROW && counter < nRow){
				
		rc = sqlite3_step(stmt);
		counter++;
		
	}
	
	val =sqlite3_column_int(stmt, nCol);
	rc =sqlite3_finalize(stmt);
	if( rc != SQLITE_OK){
		printf("Couldnt finalize:\n");
	}
	return  val;
	
		
}

const unsigned char* sqlite3_get_val_text_v2(void* p,int nCol){
	
	
	DBinfo* dbi =(DBinfo*) p;
	int rc,i, val, counter;
	const unsigned char* text_val;
	
	array =(unsigned char *) GC_malloc(1000*sizeof(char));
	
	text_val =sqlite3_column_text(dbi->ppStmt, nCol);
	memcpy(array, text_val, strlen(text_val));

	return array;
	
}



const unsigned char* sqlite3_get_val_text(void* p,const char* tbl_name,int nRow, int nCol){
	
	
	DBinfo* dbi =(DBinfo*) p;
	sqlite3_stmt* stmt;
	const char *tail;
	int rc,i, val, counter;
	const unsigned char* text_val;
	
	counter =0;
	strcpy(sql_query_buffer, "select * from ");
	strcat(sql_query_buffer, tbl_name);
	
	rc = sqlite3_prepare_v2(dbi->db_ptr, sql_query_buffer, -1, &stmt, &tail);
	if(rc != SQLITE_OK){
		fprintf(stderr, "SQL Prepare error\n");
		return NULL;
	}
	rc = sqlite3_step(stmt);

	while (rc == SQLITE_ROW && counter < nRow){

		rc = sqlite3_step(stmt);
		counter++;
		
	}


	array =(unsigned char *) GC_malloc(1000*sizeof(char));
	
	text_val =sqlite3_column_text(stmt, nCol);
	memcpy(array, text_val, sizeof(text_val));
	rc =sqlite3_finalize(stmt);
	if( rc != SQLITE_OK){
		printf("Couldn't finalize.\n");
	}

	return array;
	
}


float sqlite3_get_float(void* p,const char* tbl_name, int nRow, int nCol){
	
	DBinfo* dbi =(DBinfo*) p;
	sqlite3_stmt* stmt;
	const char *tail;
	int rc,i, val, counter;
	double double_val;
	
	
	counter =0;
	strcpy(sql_query_buffer, "select * from ");
	strcat(sql_query_buffer, tbl_name);
	
	rc = sqlite3_prepare_v2(dbi->db_ptr, sql_query_buffer, -1, &stmt, &tail);
	if(rc != SQLITE_OK){
		fprintf(stderr, "SQL Prepare error\n");
		
	}
	rc = sqlite3_step(stmt);
	
	while (rc == SQLITE_ROW && counter < nRow){
		
		
		rc = sqlite3_step(stmt);
		counter++;
		
	}
	double_val =sqlite3_column_double(stmt, nCol);
	float float_val =(float)double_val;
	rc =sqlite3_finalize(stmt);
	if( rc != SQLITE_OK){
		printf("Couldn't finalize.\n");
	}
	return float_val;
	
}

float sqlite3_get_float_v2(void* p, int nCol){
	
	DBinfo* dbi =(DBinfo*) p;
	double double_val;

	double_val =sqlite3_column_double(dbi->ppStmt, nCol);
	float float_val =(float)double_val;
	return float_val;
	
}


void sqlite3_free_table_idr(void* db){
	Table* tbl =(Table*) db;
	sqlite3_free_table(tbl->table_data);
	free(tbl);
}


int sqlite3_step_idr(void* db){
	
	DBinfo* dbi =(DBinfo*) db;
	int rc =sqlite3_step(dbi->ppStmt);
	return rc;
}

void* sqlite3_bind_int_idr(void* p,int index, int val){
	
	DBinfo* dbi =(DBinfo*) p;
	int rc;

	printf("\nThe statement has %d wildcards\n", sqlite3_bind_parameter_count(dbi->ppStmt));
	rc =sqlite3_bind_int(dbi->ppStmt,index,val);
	if(rc != SQLITE_OK){
		printf("Error in binding\n");
		return NULL;
	}

	return dbi;
}

void* sqlite3_bind_float_idr(void* p,int index, float val){
	
	DBinfo* dbi =(DBinfo*) p;
	int rc;
	double res =(float)val;

	rc =sqlite3_bind_double(dbi->ppStmt,index,res);
	
	if(rc != SQLITE_OK){
		return NULL;
	}

	return dbi;
}

int sqlite3_bind_null_idr(void* p,int index){
	
	DBinfo* dbi =(DBinfo*) p;
	int rc;
	rc =sqlite3_bind_null(dbi->ppStmt,index);
	if(rc != SQLITE_OK){
		return 1;
	}

	return rc;
}

void* sqlite3_bind_text_idr(void* p,const char* text, int index,int length){
	
	DBinfo* dbi =(DBinfo*) p;
	int rc;
	rc =sqlite3_bind_text(dbi->ppStmt,index,text,length,SQLITE_STATIC);
	if(rc != SQLITE_OK){
		printf("Error in binding\n");
		return NULL;
	}

	return dbi;
	
}
int sqlite3_column_count_idr(void* db, const char* tbl_name){
	DBinfo* dbi =(DBinfo*) db;
	sqlite3_stmt* stmt;
	const char *tail;
	int rc;

	strcpy(sql_query_buffer, "select * from ");
	strcat(sql_query_buffer, tbl_name);
	
	rc = sqlite3_prepare_v2(dbi->db_ptr, sql_query_buffer, -1, &stmt, &tail);
	if(rc != SQLITE_OK){
		fprintf(stderr, "SQL Prepare error");
		return rc;
	}
	printf("Prepare successful %d\n", rc);
	
	rc =sqlite3_column_count(stmt);
	if(rc == 0){
		fprintf(stderr, "SQL column count error\n");
		return rc;
	}
	sqlite3_finalize(stmt);

	// rc = actual column count
	return rc;
}


int sqlite3_data_count_idr(void* db){
	
	DBinfo* dbi =(DBinfo*) db;
	int rc = sqlite3_data_count(dbi->ppStmt);
	
	return rc;
	
}

int sqlite3_finalize_idr(void* db){
	
	DBinfo* dbi=(DBinfo*) db;
	int rc =sqlite3_finalize(dbi->ppStmt);
	return rc;
}

int sqlite3_complete_idr(const char *sql){
	
	int rc = sqlite3_complete(sql);
	return rc;
	
	
}
int sqlite3_reset_idr(void* db){
	
	DBinfo* dbi=(DBinfo*) db;
    int rc = sqlite3_reset(dbi-> ppStmt);
	return rc;
	
}

const char *sqlite3_column_name_idr(void* db, int N){
	
	DBinfo* dbi=(DBinfo*) db;
	const char *name = sqlite3_column_name(dbi->ppStmt, N);

	return name;
}

const char *sqlite3_column_decltype_idr(void* db,int n){
	DBinfo* dbi=(DBinfo*) db;
	const char *dectype = sqlite3_column_decltype(dbi->ppStmt, n);
	
	return dectype;
	
}


int sqlite3_column_bytes_idr(void* db, int n){
	
	DBinfo* dbi=(DBinfo*) db;
	int res = sqlite3_column_bytes(dbi->ppStmt, n);
	return res;
	
	
}

const void *sqlite3_column_blob_idr(void* db, int iCol){
	DBinfo* dbi=(DBinfo*) db;
	const void* data =sqlite3_column_blob(dbi-> ppStmt, iCol);
	return data;
}

const unsigned char *sqlite3_column_text_idr(void* db, int iCol){
	DBinfo* dbi=(DBinfo*) db;
	const unsigned char* col_text =sqlite3_column_text(dbi->ppStmt, iCol);
	return col_text;
	
}

int sqlite3_column_int_idr(void* db, int iCol){
	DBinfo* dbi=(DBinfo*) db;
	int res =sqlite3_column_int(dbi-> ppStmt, iCol);
	return res;
	
}


void* sqlite3_backup_init_idr(void* pDest,
							  const char *zDestName,
							  void* pSource,
							  const char *zSourceName
							  ){
	
	DBinfo* dbi=(DBinfo*) pDest;
	DBbackup* dbi2=(DBbackup*) pSource;
	
	void* res = sqlite3_backup_init(dbi->db_ptr,zDestName,
									dbi2->source_ptr,zSourceName);
	
	if(res == NULL){
		printf("Error number in initializing backup : %d\n", sqlite3_errcode(dbi->db_ptr));
	}
	
	dbi2->backup = res;
	return dbi2;
	
	
}

int sqlite3_backup_step_idr(void *backup, int nPage){
	
	DBbackup* dbi=(DBbackup*) backup;
	int res = sqlite3_backup_step(dbi->backup, nPage);
	
	if( res == SQLITE_OK){
		printf("Backup Success\n");
	}
	return res;
	
	
}
int sqlite3_backup_finish_idr(void *backup){
	
	DBbackup* dbi=(DBbackup*) backup;
	int res = sqlite3_backup_finish(dbi->backup);
	return res;
	
	
}

int sqlite3_backup_remaining_idr(void *backup){
	
	DBbackup* dbi=(DBbackup*) backup;
	int res = sqlite3_backup_remaining(dbi->backup);
	
	return res;
}

int sqlite3_backup_pagecount_idr(void *backup){
	
	DBbackup* dbi=(DBbackup*) backup;
	int res =sqlite3_backup_pagecount(dbi-> backup);
	return res;
	
}

int sqlite3_value_bytes_idr(void* value){
	
	DBinfo* dbi=(DBinfo*) value;
	int res = sqlite3_value_bytes(dbi->value);
	return res;
	
}

int sqlite3_value_bytes16_idr(void* value){
	
	DBinfo* dbi=(DBinfo*) value;
	int res =sqlite3_value_bytes16(dbi->value);
	return res;	
	
}

int strLength(const char * str){
	
	int length = strlen(str);
	return length;
	
	
}


