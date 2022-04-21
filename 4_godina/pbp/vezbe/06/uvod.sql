drop database if exists uvod;
create database uvod character set = utf8;
use uvod;

create table student (
    id int primary key auto_increment,
    ime varchar(50) not null,
    prezime varchar(50) not null,
    prosek float check (prosek >= 6 and prosek <= 10),
    datum_upisa date,
    upisan boolean
);

create table dodatne_informacije (
    id int primary key,
    grad varchar(30) not null,
    drzava varchar(30) not null
);

insert into student (ime, prezime, prosek, datum_upisa) 
values ('Petar', 'Petrovic', 9.87, '2020-10-10'),
       ('Marko', 'Markovic', 8.00, '2020-11-11');

select * from student;
