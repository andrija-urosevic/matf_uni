import org.apache.spark.{SparkConf, SparkContext}

object Main extends App {

  println("Unesite broj n: ")
  val n = Console.readInt()

  def fact(x: Int): Int = {
    if (x == 1)
      return 1
    return x * fact(x - 1)
  }

  val conf = new SparkConf()
    .setAppName("Spark")
    .setMaster("local[4]")
    .set("spark.driver.bindAddress", "127.0.0.1")

  val sc = new SparkContext(conf)

  val arr = (1 to n).toArray
  val arrRDD = sc.parallelize(arr)
  val factorials = arrRDD
    .map(x => fact(x))
    .collect()

  sc.stop()

  println(factorials.mkString(", "))

}
