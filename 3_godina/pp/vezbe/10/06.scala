import org.apache.spark.{SparkConf, SparkContext}

object Main extends App {

  val conf = new SparkConf()
    .setAppName("Spark")
    .setMaster("local[4]")
    .set("spark.driver.bindAddress", "127.0.0.1")

  val sc = new SparkContext(conf)

  
  val logs = sc
    .textFile("log.txt")
    .filter(_.contains("java"))
    .filter(line => line.startsWith("[info]") || 
                    line.startsWith("[error]") || 
                    line.startsWith("[warn]"))
    .map(line => {
      val words = line.split("\\s+")
      (words(0), words.drop(0).mkString(" "))
    })
    .groupByKey()
    .map(pair => (pair._1, pair._2.size))
    .collect()

  sc.stop()

  logs.foreach(log => println(log._1 + ": " + log._2))

}
