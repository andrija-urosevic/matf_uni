drop database if exists banka;
create database banka character set = utf8;
use banka;

create table racun (
    broj int not null primary key,
    kolicina dec(10, 2)
);

set @suma = 0;

delimiter $$

create trigger ukupna_suma before insert on racun
for each row
begin
    set @suma = @suma + new.kolicina;
end$$

delimiter ;

insert into racun values
    (111, 123),
    (112, 453),
    (113, 327);

insert ignore into racun values
    (112, 500);

select @suma as 'ukupno';
