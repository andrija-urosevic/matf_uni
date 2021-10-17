import java.util.Scanner
import java.util.Random
import java.util.concurrent.ConcurrentLinkedQueue
import java.util.concurrent.atomic.AtomicInteger
import java.io.File

class Cleaner(id: Int,
              rooms: ConcurrentLinkedQueue[Int],
              tip: AtomicInteger) extends Thread {

  override def run(): Unit = {

    while(!rooms.isEmpty()) {
      val roomForCleaning = rooms.poll()

      println(s"Cistacica ${id} cisti sobu ${roomForCleaning}!")

      val r = new Random()
      val sleepTime = r.nextInt(3000)
      val randomTip = r.nextInt(500)
      Thread.sleep(sleepTime)

      println(s"Cistacica ${id} je ocistila sobu ${roomForCleaning}, i zaradila ${randomTip}din!")
      tip.getAndAdd(randomTip);
    }
  }

}

object Main {
  
  def main(args: Array[String]): Unit = {

    val scFile = new Scanner(new File("sobe.txt"))
    val scStdio = new Scanner(System.in)

    val rooms = new ConcurrentLinkedQueue[Int]()
    while(scFile.hasNextInt()) {
      rooms.add(scFile.nextInt())
    }

    val tip: AtomicInteger = new AtomicInteger(0)

    println("Unesite broj cistacica: ")
    val numOfThreads = scStdio.nextInt()

    val cleaners = new Array[Cleaner](numOfThreads)

    for (i <- 0 until numOfThreads) {
      cleaners(i) = new Cleaner(i, rooms, tip)
    }

    for (cleaner <- cleaners) {
      cleaner.start()
    }

    for (cleaner <- cleaners) {
      cleaner.join()
    }

    println(s"Ukupna zarada je ${tip}!")

    scStdio.close()
    scFile.close()
  }

}
