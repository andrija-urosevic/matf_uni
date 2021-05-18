import java.io._
import java.util._
import java.util.concurrent._
import java.util.concurrent.atomic._

class Client(name: String, creditWish: Long) {

  var credit: Long = 0

  def getName = name 
  def getCreditWish = creditWish
  def getCredit = credit

  def setCredit(_credit: Long): Unit = { 
    credit = _credit
  }

}

class Employee(num: Int,
               interest: Float,
               capital: AtomicLong,
               clientsQue: ConcurrentLinkedQueue[Client],
               clientsBorrowers: ConcurrentLinkedQueue[Client]) extends Thread {
                 
  override def run(): Unit = {
    while(!clientsQue.isEmpty()) {
      val client = clientsQue.poll()
      println(s"Klijent ${client.getName} razgovara sa zaposlenim ${num}")
      Thread.sleep(ThreadLocalRandom.current().nextInt(1, 5) * 1000)

      capital.synchronized {
        if (capital.get() < client.getCreditWish) {
          println(s"Klijent ${client.getName} ne moze da dobije zeljeni kredit od ${client.getCreditWish}$$.")
        } else {
          println(s"Klijent ${client.getName} je dobijo zeljeni kredit od ${client.getCreditWish}$$.")
          capital.set(capital.get() - client.getCreditWish)
          client.setCredit((client.getCreditWish * interest).toInt)
          clientsBorrowers.add(client)
        }
      }
    }
  }

}

object Banca {

  def main(args: Array[String]):Unit = {

    val scFile: Scanner = new Scanner(new File("red_klijenata.txt"))
    val scInput: Scanner = new Scanner(System.in)

    print("Unesite pocetni kapital banke: ")
    val capital: AtomicLong = new AtomicLong(scInput.nextLong())
    print("Unesite kamatu banke: ")
    val interest: Float = scInput.nextFloat() 
    print("Unesite broj zaposlenih: ")
    val numOfEmployees: Int = scInput.nextInt()

    val clientsQue: ConcurrentLinkedQueue[Client] = new ConcurrentLinkedQueue[Client]()
    val clientsBorrowers: ConcurrentLinkedQueue[Client] = new ConcurrentLinkedQueue[Client]()
    val employees: Array[Employee] = new Array[Employee](numOfEmployees)

    while(scFile.hasNext())
      clientsQue.add(new Client(scFile.next(), scFile.nextLong()))

    for (i <- 0 until numOfEmployees) {
      employees(i) = new Employee(i, interest, capital, clientsQue, clientsBorrowers)
    }

    for (employee <- employees) {
      employee.start()
    }

    for (employee <- employees) {
      employee.join()
    }

    var newCapital: Long = 0
    val clientIter = clientsBorrowers.iterator()
    while (clientIter.hasNext) {
      newCapital += clientIter.next().getCredit
    }

    println(s"Trenutni kapital ${newCapital + capital.get}")
  }

}
