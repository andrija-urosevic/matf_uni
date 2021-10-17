import string
import random

class Chromosome(object):

    def __init__(self, dna, fitness):
        super(Chromosome, self).__init__()
        self.dna = dna
        self.fitness = fitness

    def __str__(self):
        return f"{''.join(self.dna)} -> {self.fitness}"

    def __repr__(self):
        return str(self)


class GeneticAlgorithm(object):

    def __init__(self, possible_gene_value, target_dna):
        super(GeneticAlgorithm, self).__init__()
        self.possible_gene_value = possible_gene_value

        self.population_size = 5000
        self.number_of_generations = 100
        self.chromosome_size = len(target_dna)
        self.tournament_size = 100
        self.reproduction_size = 100
        self.selection_function = self.tournament_selection
        self.mutation_rate = 0.1

        self.target = Chromosome(target_dna, self.chromosome_size)

    def calculate_fitness(self, dna):
        fitness = 0
        for i in range(self.chromosome_size):
            if dna[i] == self.target.dna[i]:
                fitness += 1
        return fitness

    def initial_population(self):
        result = []

        for _ in range(self.population_size):
            dna = random.choices(self.possible_gene_value, k=self.chromosome_size)
            fitness = self.calculate_fitness(dna)
            chromosome = Chromosome(dna, fitness)
            result.append(chromosome)

        return result

    def roulette_selection(self, population):
        ws = [chromosome.fitness for chromosome in population]
        winners = random.choices(population, weights=ws, k=1)
        return winners[0]

    def tournament_selection(self, population):
        selected = random.sample(population, self.tournament_size)
        winner = max(selected, key=lambda chromosome: chromosome.fitness)
        return winner

    def selection(self, population):
        return [self.selection_function(population)
                    for _ in range(self.reproduction_size)]

    def crossover(self, parent1, parent2):
        mid_point = random.randint(1, self.chromosome_size)

        child1_dna = parent1.dna[:mid_point] + parent2.dna[mid_point:]
        child2_dna = parent2.dna[:mid_point] + parent1.dna[mid_point:]

        return child1_dna, child2_dna

    def mutate(self, child_dna):
        if random.random() < self.mutation_rate:
            rand_index = random.randint(0, self.chromosome_size - 1)
            child_dna[rand_index] = random.choice(self.possible_gene_value)
        return child_dna


    def generate_population(self, selected):
        population = []

        for _ in range(self.population_size // 2):
            parents = random.sample(selected, 2)

            child1_dna, child2_dna = self.crossover(parents[0], parents[1])

            child1_dna = self.mutate(child1_dna)
            child2_dna = self.mutate(child2_dna)

            child1_fitness = self.calculate_fitness(child1_dna)
            child2_fitness = self.calculate_fitness(child2_dna)

            population.append(Chromosome(child1_dna, child1_fitness))
            population.append(Chromosome(child2_dna, child2_fitness))

        return population

    def best_fit(self, population):
        return max(population, key=lambda chromosome: chromosome.fitness)

    def optimal_fit(self, chromosome):
        return chromosome.fitness >= self.target.fitness - 2


    def optimize(self):
        population = self.initial_population()

        current_best = self.best_fit(population)
        current_best_generation_num = 0
        for generation_num in range(self.number_of_generations):
            selected = self.selection(population)
            population = self.generate_population(selected)
            current = self.best_fit(population)

            if current_best.fitness < current.fitness:
                current_best = current
                current_best_generation_num = generation_num

            print(current_best)
            if self.optimal_fit(current_best):
                break

            if generation_num - current_best_generation_num >= 10:
                break


        return current_best


def get_random_string(n):
    return random.choices(string.ascii_letters, k=n)


if __name__ == '__main__':
    target = get_random_string(100)
    print(f"Target: {''.join(target)}")

    genetic_algorithm = GeneticAlgorithm(string.ascii_letters, target)
    result = genetic_algorithm.optimize()
    print(result)
