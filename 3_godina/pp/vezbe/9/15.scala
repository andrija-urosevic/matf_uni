import java.util.Scanner
import java.io.PrintWriter
import java.io.File

class Transponer(row: Int, n: Int, m: Int, 
                 mat: Array[Array[Int]], 
                 mat_T: Array[Array[Int]]) extends Thread {
  
  override def run(): Unit = {
    for (j <- 0 until m) {
      mat_T(j)(row) = mat(row)(j)
    }
  }

}


object Main {

  def main(args: Array[String]): Unit = {

    val sc = new Scanner(new File("matrica.txt"))
    val pw = new PrintWriter(new File("transponovana_matrica.txt"))

    val n = sc.nextInt()
    val m = sc.nextInt()

    val mat = new Array[Array[Int]](n)
    for (i <- 0 until n) {
      mat(i) = new Array[Int](m)
      for (j <- 0 until m) {
        mat(i)(j) = sc.nextInt()
        print(mat(i)(j))
      }
      println()
    }

    val mat_T = new Array[Array[Int]](m)
    for (i <- 0 until m) {
      mat_T(i) = new Array[Int](n)
    }

    val transponers = new Array[Transponer](n)

    for (i <- 0 until n) {
      transponers(i) = new Transponer(i, n, m, mat, mat_T)
    }

    for (transponer <- transponers) {
      transponer.start()
    }

    for (transponer <- transponers) {
      transponer.join()
    }

    for (i <- 0 until m) {
      for (j <- 0 until n) {
        pw.print(mat_T(i)(j) + " ")
      }
      pw.println()
    }

    pw.close()
    sc.close()
  }

}
