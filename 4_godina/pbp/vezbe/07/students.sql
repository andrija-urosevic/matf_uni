drop database if exists test;
create database test character set = utf8;
use test;

create table student_mast (
    student_id int not null primary key,
    name varchar(20),
    st_class int default 0
);

create table student_marks (
    student_id int not null primary key,
    sub1 int check(sub1 between 0 and 100),
    sub2 int check(sub2 between 0 and 100),
    sub3 int check(sub3 between 0 and 100),
    sub4 int check(sub4 between 0 and 100),
    sub5 int check(sub5 between 0 and 100),
    total int check(total between 0 and 500),
    per_marks int check(per_marks between 0 and 100),
    grade varchar(15),
    constraint fk_id foreign key(student_id)
        references student_mast(student_id)
        on delete cascade
        on update cascade
);

create table student_log (
    log_id int not null primary key auto_increment,
    user_id varchar(50),
    description text
);

delimiter $

create trigger marks before update on student_marks
for each row begin
    set new.total = new.sub1 + new.sub2 + new.sub3 + new.sub4 + new.sub5;
    set new.per_marks = new.total / 5;
    set new.grade = case
        when new.per_marks >= 90 then 'EXCELLENT'
        when new.per_marks >= 75 then 'VERY GOOD'
        when new.per_marks >= 60 then 'GOOD'
        when new.per_marks >= 40 then 'AVERAGE'
        else 'NOT PROMOTED'
    end;
end$

create trigger update_class before update on student_mast
for each row begin
    declare msg varchar(100);
    set msg = 'Nije dozvoljeno umanjivanje razreda!';

    if (new.st_class < old.st_class) then
        signal sqlstate '45000' set message_text = msg;
    end if;
end$

create trigger update_student after update on student_mast
for each row begin
    insert into student_log (user_id, description) values (
        user(),
        concat('Azuriranje studenta: ', new.student_id)
    );
end$

create trigger delete_student after delete on student_mast
for each row begin
    insert into student_log (user_id, description) values (
        user(),
        concat('Brisanje studenta: ', old.student_id)
    );
end$

delimiter ;

insert into student_mast (student_id, name, st_class) values
    (1, 'Marko', 4),
    (2, 'Darko', 5);

update student_mast
set st_class = st_class + 1
where student_id = 1 or student_id = 2;

select * from student_mast\G

insert into student_marks (student_id) values (1), (2);

update student_marks
set sub1 = 30, sub2 = 50, sub3 = 100, sub4 = 60, sub5 = 65
where student_id = 1;

update student_marks
set sub1 = 80, sub2 = 100, sub3 = 100, sub4 = 100, sub5 = 85
where student_id = 2;

delete from student_mast where student_id = 1;

select * from student_marks\G

select * from student_log\G
