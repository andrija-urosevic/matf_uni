import org.apache.spark.{SparkConf, SparkContext}

object Main extends App {

  print("Unesite ime proizvodjaca: ")
  val manufacturer = Console.readLine()
  
  val conf = new SparkConf()
    .setAppName("Spark")
    .setMaster("local[4]")
    .set("spark.driver.bindAddress", "127.0.0.1")

  val sc = new SparkContext(conf)

  sc.textFile("uredjaji.txt")
    .filter(_.startsWith(manufacturer))
    .takeSample(false, 5)
    .foreach(println)

  sc.stop()

}
