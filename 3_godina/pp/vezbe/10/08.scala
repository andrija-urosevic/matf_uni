import org.apache.spark.{SparkConf, SparkContext}

object Main extends App {

  val conf = new SparkConf()
    .setAppName("Spark")
    .setMaster("local[4]")
    .set("spark.driver.bindAddress", "127.0.0.1")

  val sc = new SparkContext(conf)

  val winners = sc
    .textFile("zaposleni.txt")
    .filter(_.contains("IT_PROG"))
    .map(line => {
      val words = line.split("\\s+")
      (words(0), words(1), words(3))
    })
    .takeSample(false, 3, 0)

  sc.stop()

  winners.foreach(winner => println(s"${winner._1} ${winner._2} (${winner._3})"))

}
