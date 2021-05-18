import java.io._
import java.util._
import java.util.concurrent._
import scala.collection.mutable.ArrayBuffer

class CounterDNA (start: Int, end: Int, 
                  lines: ArrayBuffer[String],
                  mapDNA: ConcurrentHashMap[Char, Int]) 
  extends Thread {

    override def run(): Unit = {
      for (i <- start until end) {
        val a = lines(i).count((c: Char) => { c == 'a' })
        val c = lines(i).count((c: Char) => { c == 'c' })
        val g = lines(i).count((c: Char) => { c == 'g' })
        val t = lines(i).count((c: Char) => { c == 't' })

        mapDNA.synchronized {
          mapDNA.replace('a', mapDNA.get('a') + a)
          mapDNA.replace('c', mapDNA.get('c') + c)
          mapDNA.replace('g', mapDNA.get('g') + g)
          mapDNA.replace('t', mapDNA.get('t') + t)
        }
      }
    }

}

object DNA {

  def main(args: Array[String]): Unit = {
    val scFile: Scanner = new Scanner(new File("bio_podaci.txt"))
    val scInput: Scanner = new Scanner(System.in)

    print("Unesite broj niti: ")
    val numOfThreads = scInput.nextInt()

    val lines: ArrayBuffer[String] = new ArrayBuffer[String]()
    while(scFile.hasNextLine())
      lines.append(scFile.nextLine())

    val n = lines.length
    val step: Int = Math.ceil(n.toDouble / numOfThreads.toDouble).toInt

    val countersDNA: Array[CounterDNA] = new Array[CounterDNA](numOfThreads)
    val mapDNA: ConcurrentHashMap[Char, Int] = new ConcurrentHashMap[Char, Int](numOfThreads)
    mapDNA.put('a', 0)
    mapDNA.put('c', 0)
    mapDNA.put('t', 0)
    mapDNA.put('g', 0)

    for (i <- 0 until numOfThreads) 
      countersDNA(i) = new CounterDNA(i * step, Math.min((i+1) * step, n), lines, mapDNA)

    for (i <- 0 until numOfThreads)
      countersDNA(i).start()

    for (i <- 0 until numOfThreads)
      countersDNA(i).join()

    println(s"Broj a: ${mapDNA.get('a')}")
    println(s"Broj c: ${mapDNA.get('c')}")
    println(s"Broj t: ${mapDNA.get('t')}")
    println(s"Broj g: ${mapDNA.get('g')}")
      
  }

}
