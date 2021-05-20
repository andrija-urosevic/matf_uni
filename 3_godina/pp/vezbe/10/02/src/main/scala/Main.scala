import org.apache.spark.SparkConf
import org.apache.spark.SparkContext

object Main extends App {

  val conf = new SparkConf()
    .setAppName("Broj Petocifrenih")
    .setMaster("local[4]")
    .set("spark.driver.bindAddress", "127.0.0.1")

  val sc = new SparkContext(conf)

  val dataRDD = sc.textFile("brojevi.txt")

  val arrData = dataRDD.take(10)
  
  val count5DigitNumber = dataRDD
    .filter(_.length == 5)
    .count()

  sc.stop()
  
  println(count5DigitNumber)
  println(arrData.mkString(", "))

}
