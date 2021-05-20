import org.apache.spark.{SparkConf, SparkContext}

object Main extends App {
  
  val conf = new SparkConf()
    .setAppName("Spark")
    .setMaster("local[4]")
    .set("spark.driver.bindAddress", "127.0.0.1")

  val sc = new SparkContext(conf)

  sc.textFile("knjiga.txt")
    .flatMap(_.split("\\s+"))
    .filter(word => word == "0" || 
                    word == "1" ||
                    word == "2" ||
                    word == "3" ||
                    word == "4" ||
                    word == "5" ||
                    word == "6" ||
                    word == "6" ||
                    word == "8" ||
                    word == "9")
    .map(digit => (digit, 1))
    .reduceByKey((acc, x) => acc + x)
    .sortByKey()
    .collect()
    .foreach(println)

  sc.stop()

}
