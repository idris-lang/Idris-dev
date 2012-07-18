#include <stdio.h>
#include <string.h>
#include <sqlite3.h>

sqlite3* db; // pointer to the database

int first_row;

int select_callback(void *p_data, int num_fields, char **p_fields, char **p_col_names) {
	
	int i; // counter
	int *p_rn =(int*)p_data; // pointer counter
	
	if(first_row) {
		first_row=0;
		// Go through the columns
		for(int i=0; i<num_fields; i++){
			printf("%20s", p_col_names[i]);
		}
		printf("\n");
		for(i=0; i<num_fields; i++){
			printf("=");
		}
		printf("\n");
	}
	(*p_rn)++; // increment the pointer counter for column 
	
	
	for(i=0; i< num_fields; i++){
		printf("%20s", p_fields[i]);
	}
	printf("\n");
	return 0;
}
void select_stmt(const char* stmt){
	char *errmsg; // erro
	int ret;	// return code
	int nrecs =0; // return code 0 for successful
	
	first_row =1;
	
	// open database, SQL to be evaluated, call back function, 1st argument to call back ,err
	ret = sqlite3_exec(db, stmt, select_callback, &nrecs, &errmsg);
	if(ret !=SQLITE_OK){
		printf("Error in select statement %s [%s].\n", stmt, errmsg);
	}
	else{
		printf("\n	%d records returned.\n", nrecs);
	}
}

void sql_stmt(const char* stmt){
	
	char *errmsg;
	int ret;
	ret = sqlite3_exec(db, stmt, 0, 0, &errmsg);
	
	if(ret !=SQLITE_OK){
		printf("Error in select statement %s [%s].\n", stmt, errmsg);
	}
}


void insert(){
	sql_stmt("begin");
	sql_stmt("insert into Student values ('Alice','Peterson',1234551,'Medicine',12)");
	//sql_stmt("insert into mytable values ('mytable2' ,  251826,   22660136)");
	//sql_stmt("insert into mytable values ('mytable3' ,  271826,   22684136)");
	sql_stmt("commit");
}

int main(){ 
	sqlite3_open("./students.db", &db);
	
	if(db ==0 ){
		printf("Could not open the database");
		return 1;
	}
	
	//sql_stmt("Create table Student (Name, Surname, Passport ,School, School Student)");
	//insert();
//	select_stmt("Select *from Student;");
//	select_stmt("Select *from Module;");
//	select_stmt("Select *from Enrollment;");
	select_stmt("SELECT student.name FROM student, module, enrollment WHERE module.credits = 30 AND student.school_student = enrollment.school_student AND student.school = enrollment.school AND enrollment.code = module.code");
	
	
	sqlite3_close(db);
	return 0;
}







