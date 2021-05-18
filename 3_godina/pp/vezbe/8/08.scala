import java.io._
import java.util._
import java.util.concurrent._
import scala.collection.mutable.HashMap
import scala.collection.mutable.ArrayBuffer

class Gambler(name: String, 
              money: Int, 
              ticket: HashMap[String, Char],
              matches: HashMap[String, MatchQuotas]) extends Thread {

  var wonMoney: Float = 0
  
  override def run(): Unit = {

    matches.synchronized {
      matches.wait()
    }

    var countGoodPlays: Int = 0
    var totalQuota: Float = 0
    for ((m, play) <- ticket) {
      val gameMatch = matches(m)
      if (gameMatch.getResult == play) {
        countGoodPlays += 1
        println(s"Kladionicar ${name} je pogodio utakmicu ${m}, rezultatom ${play}!")
        if (gameMatch.getResult == '1') {
          totalQuota += gameMatch.getQuota1
        }
        if (gameMatch.getResult == 'x') {
          totalQuota += gameMatch.getQuotaX
        }
        if (gameMatch.getResult == '2') {
          totalQuota += gameMatch.getQuota2
        }
      }
    }

    if (countGoodPlays != 0) {
      wonMoney = totalQuota * money / countGoodPlays
    }

  }

  def getWonMoney: Float = wonMoney
  def getGambler: String = name

}

class MatchQuotas(quota1: Float, quotaX: Float, quota2: Float) {

  var result: Char = 'x'

  def getQuota1: Float = quota1
  def getQuotaX: Float = quotaX
  def getQuota2: Float = quota2

  def getResult: Char = result 

  def setResult(res: Char): Unit = {
    result = res
  }
}

object Gambling {

  def main(args: Array[String]): Unit = {

    val scTickets: Scanner = new Scanner(new File("kladionicari.txt"))
    val scMatch: Scanner = new Scanner(new File("utakmice.txt"))

    val matches: HashMap[String, MatchQuotas] = new HashMap[String, MatchQuotas]()
    val gamblers: ArrayBuffer[Gambler] = new ArrayBuffer[Gambler]();

    while (scMatch.hasNextLine) {
      val name: String = scMatch.nextLine()
      val matchQuotas: MatchQuotas = new MatchQuotas(scMatch.nextFloat(), 
                                                     scMatch.nextFloat(), 
                                                     scMatch.nextFloat())
      matches.put(name, matchQuotas)
      scMatch.nextLine()
    }

    while(scTickets.hasNext) {
      val name: String = scTickets.next()
      val money: Int = scTickets.nextInt()
      val ticket: HashMap[String, Char] = new HashMap[String, Char]()
      for (i <- 0 until 5) {
        scTickets.nextLine()
        val matchGame: String = scTickets.nextLine()
        val play: Char = scTickets.next()(0)
        ticket.put(matchGame, play)
      }
      gamblers.append(new Gambler(name, money, ticket, matches))
    }

    for (gambler <- gamblers) {
      gambler.start()
    }

    println("Utakmice se igraju!")
    Thread.sleep(1000)

    for ((_, q) <- matches) {
      val res = ThreadLocalRandom.current().nextInt(0, 3)
      if (res != 0) 
        q.setResult(res.toString()(0))
    }

    matches.synchronized {
      matches.notifyAll()
    }

    for (gambler <- gamblers) {
      gambler.join()
    }

    for (gambler <- gamblers) {
      val wonMoney = gambler.getWonMoney
      val name = gambler.getGambler
      println(s"Kladionicar ${name} je osvojio ${wonMoney}")
    }

  }

}
