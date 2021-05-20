import org.apache.spark.{SparkConf, SparkContext}

object Main extends App {
  
  println("Unesite broj n: ")
  val n = Console.readInt()

  val conf = new SparkConf()
    .setAppName("Spark")
    .setMaster("local[4]")
    .set("spark.driver.bindAddress", "127.0.0.1")

  val sc = new SparkContext(conf)

  val arr = (1 to n).toArray
  val arrRDD = sc.parallelize(arr)
  val harmonic = arrRDD
    .map(x => 1.0 / x.toFloat)
    .sum()

  sc.stop()

  println(harmonic)

}
