import java.util.concurrent._
import java.util.Scanner

class Konobar(ime : String, brStolova : Int) extends Thread {

  override def run() : Unit = {
    for (i <- 0 until brStolova) {
      Thread.sleep(ThreadLocalRandom.current().nextInt(1, 10) * 1000);
      println("Konobar " + ime + " je usluzio " + i + ". sto.");
    }
    println("Konobar " + ime + " je usluzio sve stolove!");
  }

}

object Restoran {

  def main(args: Array[String]) : Unit = {

    val sc : Scanner = new Scanner(System.in);

    print("Unesite broj stolova: ");
    val brojStolova = sc.nextInt();

    val brojStolovaPoKonobaru = Math.ceil(brojStolova / 5.0).toInt;

    val pera = new Konobar("Pera", brojStolovaPoKonobaru);
    val mika = new Konobar("Mika", brojStolovaPoKonobaru);
    val laza = new Konobar("Laza", brojStolovaPoKonobaru);
    val maza = new Konobar("Maza", brojStolovaPoKonobaru);
    val mara = new Konobar("Mara", brojStolova - 4 * brojStolovaPoKonobaru);

    pera.start();
    mika.start();
    laza.start();
    maza.start();
    mara.start();
  }

}
