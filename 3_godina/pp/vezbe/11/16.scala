import org.apache.spark.{SparkConf, SparkContext}

object Main extends App {
  
  val conf = new SparkConf()
    .setAppName("Spark")
    .setMaster("local[4]")
    .set("spark.driver.bindAddress", "127.0.0.1")

  val sc = new SparkContext(conf)

  sc.textFile("mavenLog.txt")
    .filter(_.startsWith("Downloaded:"))
    .filter(_.contains("apache"))
    .map(line => {
      val data = line.split("\\s+")
      (data(1), data(2).drop(1))
    })
    .saveAsTextFile("ApacheDownloaded")

  sc.stop()

}
