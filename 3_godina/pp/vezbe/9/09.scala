import java.util._
import java.util.concurrent._

class VectorSum(start: Int, end: Int, 
                v1: Array[Int], 
                v2: Array[Int]) extends Thread {

  override def run(): Unit = {
    for (i <- start until end) {
      v1(i) = v1(i) + v2(i)
    }
  }

}

object VectorSum {

  def main(args: Array[String]): Unit = {

    val sc: Scanner = new Scanner(System.in)

    print("Unesite duzinu vektora: ")
    val vectorLength = sc.nextInt()

    val v1: Array[Int] = new Array[Int](vectorLength)
    val v2: Array[Int] = new Array[Int](vectorLength)

    print("Unesite elemente za v1: ")
    for (i <- 0 until vectorLength) {
      v1(i) = sc.nextInt()
    }

    print("Unesite elemente za v2: ")
    for (i <- 0 until vectorLength) {
      v2(i) = sc.nextInt()
    }

    print("Unesite broj niti: ")
    val numThread = sc.nextInt()

    val vectorSumThreads = new Array[VectorSum](numThread)

    val step = Math.ceil(vectorLength.toFloat / numThread.toFloat).toInt

    for (i <- 0 until numThread) {
      vectorSumThreads(i) = 
        new VectorSum(i * step, Math.min((i+1) * step, vectorLength), v1, v2)
    }

    for (vectorSumThread <- vectorSumThreads) {
      vectorSumThread.start()
    }

    for (vectorSumThread <- vectorSumThreads) {
      vectorSumThread.join()
    }

    print("v1 + v2: ")
    for (e <- v1) {
      print(s"$e ")
    }

  }

}
