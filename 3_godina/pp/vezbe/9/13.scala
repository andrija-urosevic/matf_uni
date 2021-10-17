import java.util.Scanner

class ScalarMultiplier(vec: Array[Int], scalar: Int, 
                       start: Int, end: Int) extends Thread {

  override def run(): Unit = {
    for (i <- start until end) {
      vec(i) *= scalar
    }
  }

}
object Main {

  def main(args: Array[String]): Unit = {
    val sc: Scanner = new Scanner(System.in)

    print("Unesite velicinu vektora: ")
    val n: Int = sc.nextInt()

    val vec: Array[Int] = new Array[Int](n)

    print("Unesite elemente vektora: ")
    for (i <- 0 until n) {
      vec(i) = sc.nextInt()
    }

    print("Unesite skalar: ")
    val scalar: Int = sc.nextInt()

    print("Unesite broj niti: ")
    val numOfThreads: Int = sc.nextInt()

    val scalarMultipliers: Array[ScalarMultiplier] = 
      new Array[ScalarMultiplier](numOfThreads)

    val step: Int = Math.ceil(n.toDouble / numOfThreads.toDouble).toInt

    for (i <- 0 until numOfThreads) {
      scalarMultipliers(i) = new ScalarMultiplier(vec, scalar, i*step, Math.min((i+1)*step, n))
    }

    for (scalarMultiplier <- scalarMultipliers) {
      scalarMultiplier.start()
    }

    for (scalarMultiplier <- scalarMultipliers) {
      scalarMultiplier.join()
    }

    println("Rezultat: ")
    for (el <- vec) {
      print(el + " ")
    }
  }

}
