create table nabavka (
    sifra_nabavke int primary key,
    datum int check (datum between 1 and 365) not null,
    kolicina int unsigned not null,
    cena int unsigned not null,
    sifra_robe int reference roba(sifra_robe) on delete cascade,
    unique (datum, sifra_robe)
);

alter table nabavka
    add check (
        not exists(
            select * 
            from nabavka as n1
            where n1.cena > 1.1 * (
                select n2.cena 
                from nabavka as n2
                where n1.sifra_robe = n2.sifra_robe and
                    n2.datum in (
                        select max(n3.datum)
                        from nabavka as n3
                        where n3.sifra_robe = n1.sifra_robe and
                            n3.datum < n1.datum
                    )
            )
        )
    );
