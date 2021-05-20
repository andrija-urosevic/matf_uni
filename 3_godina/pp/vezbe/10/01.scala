import org.apache.spark.SparkConf
import org.apache.spark.SparkContext

object EvenSquares {

  def main(args: Array[String]): Unit = {

    val n = scala.io.StdIn.readInt()

    val conf = new SparkConf()
      .setAppName("Even Squares")
      .setMaster("local[4]")
      .set("spark.driver.bindAddress", "127.0.0.1")

    val sc = new SparkContext(conf)

    val evens = (2 to n by 2).toArray
    val evensRDD = sc.parallelize(evens)
    val evenSquares = evensRDD
      .map(x => x * x)
      .take(10)

    sc.stop()

    println(evenSquares.mkString(", "))
  }

}
