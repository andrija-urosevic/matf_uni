import java.util._
import java.io._
import org.apache.spark.{SparkConf, SparkContext}

object Main extends App {

  val conf = new SparkConf()
    .setAppName("Spark")
    .setMaster("local[4]")
    .set("spark.driver.bindAddress", "127.0.0.1")

  val sc = new SparkContext(conf)

  sc.textFile("uredjaji.txt")
    .map(line => {
      val words = line.split("\\s+")
      (words(0), words.drop(1).mkString("; "))
    })
    .groupByKey()
    .foreach(pair => {
      val pw = new PrintWriter(pair._1.toLowerCase() + ".txt")
      pw.write("---" + pair._1 + "---\n")
      pair._2.foreach(spec => pw.write(spec + "\n"))
      pw.close()
    })

  sc.stop()

}
