import org.apache.spark.{SparkConf, SparkContext}

object Main extends App {

  val conf = new SparkConf()
    .setAppName("Spark")
    .setMaster("local[4]")
    .set("spark.driver.bindAddress", "127.0.0.1")

  val sc = new SparkContext(conf)

  val koordinate = sc
    .textFile("insurance.csv")
    .flatMap(_.split("\n"))
    .filter(line => line.contains("Residential") 
                 || line.contains("Wood")
                 || line.contains("PALM BREACH COUNTRY"))
    .map(line => {
      val items = line.split(",")
      (items(3).toDouble, items(4).toDouble)
    })

  val n = koordinate.count()
  val koord_x_sum = koordinate.map(_._1).sum()
  val koord_y_sum = koordinate.map(_._2).sum()

  val avg_x_y = koordinate.reduce((a, b) => (a._1 + b._1, a._2 + b._2))

  sc.stop()

  println(n)
  println(avg_x_y._1 / n, avg_x_y._2 / n)
  println(koord_x_sum / n, koord_y_sum / n)

}
