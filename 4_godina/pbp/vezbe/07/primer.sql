drop database if exists test;
create database test character set = utf8;
use test;

create table test1 (a1 int);

create table test2 (a2 int);

create table test3 (a3 int not null primary key);

create table test4 (
    a4 int not null primary key,
    b4 int default 0
);

delimiter $$

create trigger test after insert on test1
for each row begin
    insert into test2 set a2 = new.a1;
    delete from test3 where a3 = new.a1;
    update test4 set b4 = b4 + 1 where a4 = new.a1;
end$$

delimiter ;

insert into test3 values (1), (2), (4), (5);

insert into test4 (a4) values (2), (3), (4);

insert into test1 values (1), (2), (3);

select * from test1;
select * from test2;
select * from test3;
select * from test4;

