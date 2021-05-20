import org.apache.spark.{SparkConf, SparkContext}

object Main extends App {

  val conf = new SparkConf()
    .setAppName("Spark")
    .setMaster("local[4]")
    .set("spark.driver.bindAddress", "127.0.0.1")

  val sc = new SparkContext(conf)

  sc.textFile("temperatura.txt")
    .map(line => {
      val data = line.split("\\s")
      (data(3), (data(1), data(2), data(4).toFloat))
    })
    .aggregateByKey((0.0, 0))(
      (acc, v) => (acc._1 + v._3, acc._2 + 1), 
      (acc1, acc2) => (acc1._1 + acc2._1, acc1._2 + acc2._2)
    )
    .map(pair => (pair._1, pair._2._1 / pair._2._2))
    .sortByKey()
    .collect()
    .foreach(println)

  sc.stop()

}
