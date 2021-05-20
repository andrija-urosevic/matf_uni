import org.apache.spark.{SparkConf, SparkContext}

object Main extends App {

  val conf = new SparkConf()
    .setAppName("Spark")
    .setMaster("local[4]")
    .set("spark.driver.bindAddress", "127.0.0.1")

  val sc = new SparkContext(conf)

  val knjigaRDD = sc.textFile("knjiga.txt")

  knjigaRDD.flatMap(_.split(" "))
    .map(word => (word, 1))
    .reduceByKey((x, y) => x + y)
    .sortByKey()
    .saveAsTextFile("BrojPojavljivanja")
  

  sc.stop()

}
