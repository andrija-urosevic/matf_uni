import org.apache.spark.{SparkConf, SparkContext}

object Main extends App {
  
  val conf = new SparkConf()
    .setAppName("Spark")
    .setMaster("local[4]")
    .set("spark.driver.bindAddress", "127.0.0.1")

  val sc = new SparkContext(conf)

  val v1RDD = sc
    .textFile("vektor1.txt")
    .flatMap(_.split(", *"))
    .map(_.toInt)

  val v2RDD = sc
    .textFile("vektor2.txt")
    .flatMap(_.split(", *"))
    .map(_.toInt)
  
  val v = v1RDD
    .zip(v2RDD)
    .map(pair => pair._1 + pair._2)
    .collect()

  sc.stop()

  println(v.mkString(", "))

}
