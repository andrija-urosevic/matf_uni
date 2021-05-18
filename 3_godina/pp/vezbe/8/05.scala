import java.util.Scanner
import java.io._
import scala.Array._


//nXm       mXk    nXk
//*****     **     **
//*****     **     **
//*****     **     **
//          **
//          **
class Mnozilac(vrsta : Array[Int],
               mat2  : Array[Array[Int]],
               res   : Array[Int]) extends Thread {

  val m : Int = vrsta.length;
  val k : Int = mat2(0).length;

  override def run() : Unit = {


    for (i <- 0 until k) {
      res(i) = skalarniProizvod(i);
    }

  }

  def skalarniProizvod(j : Int) : Int = {
    var r : Int = 0;
    for (i <- 0 until m) {
      r += vrsta(i) * mat2(i)(j);
    }
    return r;
  }
  
}

object MnozenjeMatrica {

  def main(args: Array[String]) : Unit = {

    val sc1 : Scanner = new Scanner(new File("mat1.txt"));
    val sc2 : Scanner = new Scanner(new File("mat2.txt"));
    val pw : PrintWriter = new PrintWriter(new File("mat3.txt"));

    val n = sc1.nextInt();
    val m1 = sc1.nextInt();
    val m2 = sc2.nextInt();
    val k = sc2.nextInt();

    if (m1 != m2) {
      println(s"Nije odgovarajuca velicina matrica: ($n, $m1) i ($m2, $k)");
      return
    }

    val mat1 = ofDim[Int](n, m1);
    val mat2 = ofDim[Int](m2, k);
    val res  = ofDim[Int](n, k);

    for (i <- 0 until n) {
      for (j <- 0 until m1) {
        mat1(i)(j) = sc1.nextInt();
      }
    }

    for (i <- 0 until m2) {
      for (j <- 0 until k) {
        mat2(i)(j) = sc2.nextInt();
      }
    }

    val mnozioci : Array[Mnozilac] = new Array[Mnozilac](n);
    for (i <- 0 until n) {
      mnozioci(i) = new Mnozilac(mat1(i), mat2, res(i));
    }

    for (i <- 0 until n) {
      mnozioci(i).start();
    }

    for (i <- 0 until n) {
      mnozioci(i).join();
    }

    println("OK!");
    pw.append(s"$n $k\n");
    for (i <- 0 until n) {
      for (j <- 0 until k) {
        pw.append(s"${res(i)(j)} ");
      }
      pw.append("\n");
    }
    pw.close();

  }

}
