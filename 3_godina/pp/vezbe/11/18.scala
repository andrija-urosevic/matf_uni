import org.apache.spark.{SparkConf, SparkContext}

object Main extends App {

  val conf = new SparkConf()
    .setAppName("Spark")
    .setMaster("local[4]")
    .set("spark.driver.bindAddress", "127.0.0.1")

  val sc = new SparkContext(conf)

  val incomes = sc
    .textFile("zaposleni.txt")
    .filter(_.contains("IT_PROG"))
    .map(line => {
      val data = line.split("\\s+")
      data(7).replace(',', '.').toFloat
    })
    .cache()

  val avgIncome = incomes.sum() / incomes.count().toFloat

  sc.stop()
  
  println(avgIncome)

}
