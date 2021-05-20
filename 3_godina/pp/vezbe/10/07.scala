import org.apache.spark.{SparkConf, SparkContext}

object Main extends App {

  val conf = new SparkConf()
    .setAppName("Spark")
    .setMaster("local[4]")
    .set("spark.driver.bindAddress", "127.0.0.1")

  val sc = new SparkContext(conf)

  val downloadings = sc
    .textFile("mavenLog.txt")
    .filter(line => line.startsWith("Downloading") || 
                    line.startsWith("Downloaded"))
    .cache()

  val numDownloading = downloadings.filter(_.startsWith("Downloading")).count()
  val numDownloaded = downloadings.filter(_.startsWith("Downloaded")).count()
  
  sc.stop()

  println(s"Zapocetno preuzimanja je $numDownloading, dok je zavrseno $numDownloaded!")

}
