import java.io._
import java.util._
import java.util.concurrent._

class FiveDigitNumberFinder(filename: String) extends Thread {

  var total5DigitNum: Int = 0

  override def run(): Unit = {

    val sc: Scanner = new Scanner(new File(filename))

    while (sc.hasNextInt) {
      val digit = sc.nextInt()
      if (digit >= 10000 && digit < 100000)
        total5DigitNum += 1
    }

  }

  def getTotal5Num: Int = total5DigitNum
  def getFilename: String = filename

}

object FiveDigitNumber {

  def main(args: Array[String]): Unit = {

    val sc: Scanner = new Scanner(System.in)

    print("Unesite broj datoteka: ")
    val numOfFiles: Int = sc.nextInt()

    val finders: Array[FiveDigitNumberFinder] = 
      new Array[FiveDigitNumberFinder](numOfFiles)

    print("Unesite imena datoteka: ")
    for (i <- 0 until numOfFiles) {
      finders(i) = new FiveDigitNumberFinder(sc.next())
    }

    for (finder <- finders) {
      finder.start()
    }

    for (finder <- finders) {
      finder.join()
    }

    for (finder <- finders) {
      val filename = finder.getFilename
      val total5DigitNum = finder.getTotal5Num
      println(s"Datoteka $filename ima $total5DigitNum petocifrenih brojeva!")
    }
  }

}
