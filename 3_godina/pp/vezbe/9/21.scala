import java.util.Scanner
import java.io.File
import java.util.concurrent._
import java.util.concurrent.atomic.AtomicInteger
import scala.collection.mutable.ArrayBuffer

class Ticket(num1: Int, num2: Int, num3: Int) {

  var n1 = num1
  var n2 = num2
  var n3 = num3

  def setNum1(v: Int): Unit = {
    n1 = v 
  }

  def setNum2(v: Int): Unit = {
    n2 = v 
  }

  def setNum3(v: Int): Unit = {
    n3 = v
  }

  def getNum1: Int = n1
  def getNum2: Int = n2
  def getNum3: Int = n3

}

class Player(name: String,
             ticket: Ticket,
             winTicket: Ticket,
             winnerCapitalStart: Int,
             winnerCapital: AtomicInteger) extends Thread {

  override def run(): Unit = {

    winTicket.synchronized{
      winTicket.wait()
    }

    var numMatched = 0
    if (ticket.getNum1 == winTicket.getNum1)
      numMatched += 1

    if (ticket.getNum2 == winTicket.getNum2)
      numMatched += 1

    if (ticket.getNum3 == winTicket.getNum3)
      numMatched += 1

    if (numMatched == 3) {
      val won = winnerCapitalStart
      winnerCapital.getAndAdd(-won)
      println(s"Igrac ${name} je osvojio ${won}")
    }

    if (numMatched == 2) {
      val won = (winnerCapitalStart * 0.4).toInt
      winnerCapital.getAndAdd(-won)
      println(s"Igrac ${name} je osvojio ${won}")
    }

    if (numMatched == 1) {
      val won = (winnerCapitalStart * 0.1).toInt
      winnerCapital.getAndAdd(-won)
      println(s"Igrac ${name} je osvojio ${won}")
    }

  }

}

object Main {

  def main(args: Array[String]): Unit = {
    val scFile = new Scanner(new File("ucesnici.txt"))
    val scStdio = new Scanner(System.in)

    println("Unesite nagradni fond: ")
    val winnerCapitalStart = scStdio.nextInt()
    val winnerCapital: AtomicInteger = new AtomicInteger(winnerCapitalStart)

    val players = new ArrayBuffer[Player]()
    val winnerTicket = new Ticket(0, 0, 0)

    while (scFile.hasNext()) {
      val name = scFile.next()
      val num1 = scFile.nextInt()
      val num2 = scFile.nextInt()
      val num3 = scFile.nextInt()
      scFile.nextLine()
      players.append(new Player(name, new Ticket(num1, num2, num3), winnerTicket, winnerCapitalStart, winnerCapital))
    }

    for (player <- players) {
      player.start()
    }

    println("Loto izvlacenje!")
    Thread.sleep(2000)

    winnerTicket.setNum1(ThreadLocalRandom.current().nextInt(1, 37))
    winnerTicket.setNum2(ThreadLocalRandom.current().nextInt(1, 37))
    winnerTicket.setNum3(ThreadLocalRandom.current().nextInt(1, 37))
    println(s"Trenutno izvuceno kolo: ${winnerTicket.getNum1}, ${winnerTicket.getNum2}, ${winnerTicket.getNum3}")

    winnerTicket.synchronized{
      winnerTicket.notifyAll()
    }

    for (player <- players) {
      player.join()
    }

    println(s"Trenutna vrednost kapitala je ${winnerCapital.get()}")

    scStdio.close()
    scFile.close()
  }

}
