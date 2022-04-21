drop database if exists fudbal;
create database fudbal character set=utf8;
use fudbal;

create table tim (
    sifra_tima int primary key,
    naziv varchar(50) not null,
    mesto varchar(50) not null
);

create table utakmica (
    sifra_utakmice int primary key,
    sifra_domacina int not null,
    sifra_gosta int not null,
    kolo int not null check (kolo >= 1 and kolo <= 42),
    ishod char(1) not null check (ishod in ('X', '1', '2')),
    godina int not null,
    constraint fk_sifratima1 foreign key(sifra_domacina)
        references tim(sifra_tima)
        on delete cascade,
    constraint fk_sifratima2 foreign key(sifra_gosta)
        references tim(sifra_tima)
        on delete cascade,
    check (sifra_domacina <> sifra_gosta),
    unique(sifra_domacina, sifra_gosta)
);
