import java.io._
import java.util._
import java.util.concurrent._
import java.util.concurrent.atomic._

class Student(studentID: Int, 
              fruits: ConcurrentLinkedQueue[Fruit],
              storage: AtomicIntegerArray) extends Thread {

  override def run(): Unit = {

    while (!fruits.isEmpty()) {
      val fruit = fruits.poll()
      println(s"Student $studentID bere ${fruit.getType}!")
      Thread.sleep(ThreadLocalRandom.current().nextInt(1, fruit.getNumTrees) * 1000)
      println(s"Student $studentID je obrao ${fruit.getType}!")
      for (i <- 0 until fruit.getNumTrees) {
        val harvested = ThreadLocalRandom.current().nextInt(50, 80)
        if (fruit.getType == "tresnje")
          storage.getAndAdd(0, harvested)
        else if (fruit.getType == "kruske")
          storage.getAndAdd(1, harvested)
        else if (fruit.getType == "kajsije")
          storage.getAndAdd(2, harvested)
        else if (fruit.getType == "sljive")
          storage.getAndAdd(3, harvested)
      }
    }

  }

}

class Fruit(fruitType: String, numTrees: Int) {

  def getType: String = fruitType
  def getNumTrees: Int = numTrees

}

object Harvest {

  def main(args: Array[String]): Unit = {
    val sc: Scanner = new Scanner(System.in)
    val scFruits: Scanner = new Scanner(new File("drvoredi.txt"))

    print("Unesite broj studenata: ")
    val numStudents = sc.nextInt()

    val students: Array[Student] = new Array[Student](numStudents)
    val fruits: ConcurrentLinkedQueue[Fruit] = 
      new ConcurrentLinkedQueue[Fruit]()
    val storage: AtomicIntegerArray = new AtomicIntegerArray(4)

    storage.set(0, 0)
    storage.set(1, 0)
    storage.set(2, 0)
    storage.set(3, 0)

    while (scFruits.hasNext) {
      val fruitType = scFruits.next() 
      val numTrees = scFruits.nextInt()
      fruits.add(new Fruit(fruitType, numTrees))
    }

    for (i <- 0 until numStudents) {
      students(i) = new Student(i, fruits, storage)
    }

    for (student <- students) {
      student.start()
    }

    for (student <- students) {
      student.join()
    }

    println("Skladiste: ")
    println(s"Ukupno obra tresnja: ${storage.get(0)}")
    println(s"Ukupno obra kruska: ${storage.get(1)}")
    println(s"Ukupno obra kajsija: ${storage.get(2)}")
    println(s"Ukupno obra sljiva: ${storage.get(3)}")
  }

}
