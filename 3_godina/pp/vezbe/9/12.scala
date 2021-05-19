import java.io._
import java.util._
import java.util.concurrent._

class Client(name: String, cost: Int, winners: Array[String]) extends Thread{

  override def run(): Unit = {
    winners.synchronized {
      winners.wait()
    }
  }

  def getClientName: String = name

}

object FlyProgrammer {

  def main(args: Array[String]): Unit = {

    val scClients = new Scanner(new File("ucesnici.txt"))

    val numClients = scClients.nextInt(); scClients.nextLine()

    val clients: Array[Client] = new Array[Client](numClients)
    val winners: Array[String] = new Array[String](5);

    for (i <- 0 until numClients) {
      val name = scClients.nextLine()
      val cost = scClients.nextInt(); scClients.nextLine()
      clients(i) = new Client(name, cost, winners)
    }

    for (client <- clients) {
      client.start()
    }

    println("Izvlacenje pobednika!")
    winners.synchronized {
      for (i <- 0 until 5) {
        val randIndex = ThreadLocalRandom.current().nextInt(0, numClients)
        winners(i) = clients(randIndex).getClientName
        Thread.sleep(1000)
      }
      winners.notifyAll()
    }

    for (client <- clients) {
      client.join()
    }

    println("Dobitnici vaucera: ")
    for (i <- 0 until 5) {
      if (i != 4)
        print(s"${winners(i)}, ")
      else
        print(winners(i))
    }
    println()

  }

}
