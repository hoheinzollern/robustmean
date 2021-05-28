# inspiration from https://www.edureka.co/blog/naive-bayes-tutorial/
# data from https://www.kaggle.com/kumargh/pimaindiansdiabetescsv

import csv
import math
import random
from scipy import stats
 
def loadCsv(filename):
    lines = csv.reader(open(r'pima-indians-diabetes.csv'))
    dataset = list(lines)
    for i in range(len(dataset)):
        dataset[i] = [float(x) for x in dataset[i]]
    #print(dataset)
    return dataset

def splitDataset(dataset, splitRatio):
    trainSize = int(len(dataset) * splitRatio)
    trainSet = []
    copy = list(dataset)
    while len(trainSet) < trainSize:
        index = random.randrange(len(copy))
        trainSet.append(copy.pop(index))
    return [trainSet, copy]
   
#Separate Data By Class
def separateByClass(dataset):
    separated = {}
    for i in range(len(dataset)):
        vector = dataset[i]
        if (vector[-1] not in separated):
            separated[vector[-1]] = []
        separated[vector[-1]].append(vector)
    return separated

#Calculate Mean
def mean(numbers):
    trimmed_mean = stats.trim_mean(numbers, 0.1)
    return trimmed_mean
    #return sum(numbers)/float(len(numbers))

#Calculate Standard Deviation
def stdev(numbers):
    avg = mean(numbers)
    variance = sum([pow(x-avg,2) for x in numbers])/float(len(numbers)-1)
    return math.sqrt(variance)

#Summarize Dataset
def summarize(dataset):
    summaries = [(mean(attribute), stdev(attribute)) for attribute in zip(*dataset)]
    del summaries[-1]
    return summaries

#Summarize Attributes By Class
def summarizeByClass(dataset):
    separated = separateByClass(dataset)
    summaries = {}
    for classValue, instances in separated.items():
        summaries[classValue] = summarize(instances)
    return summaries

# Calculate Gaussian Probability Density Function
def calculateProbability(x, mean, stdev):
    exponent = math.exp(-(math.pow(x-mean,2)/(2*math.pow(stdev,2))))
    return (1/(math.sqrt(2*math.pi)*stdev))*exponent

# Calculate Class Probabilities
def calculateClassProbabilities(summaries, inputVector):
    probabilities = {}
    for classValue, classSummaries in summaries.items():
        probabilities[classValue] = 1
        for i in range(len(classSummaries)):
            mean, stdev = classSummaries[i]
            x = inputVector[i]
            probabilities[classValue] *= calculateProbability(x, mean, stdev)
    return probabilities

# Make a Prediction
def predict(summaries, inputVector):
    probabilities = calculateClassProbabilities(summaries, inputVector)
    bestLabel, bestProb = None, -1
    for classValue, probability in probabilities.items():
        if bestLabel is None or probability > bestProb:
            bestProb = probability
            bestLabel = classValue
    return bestLabel

# Make Predictions
def getPredictions(summaries, testSet):
    predictions = []
    for i in range(len(testSet)):
        result = predict(summaries, testSet[i])
        predictions.append(result)
    return predictions

# Get Accuracy
def getAccuracy(testSet, predictions):
    correct = 0
    for x in range(len(testSet)):
        if testSet[x][-1] == predictions[x]:
            correct += 1
    return (correct/float(len(testSet)))*100.0


def pollute(dataset, column_idx, no_of_rows):
    # pollute front
    for tupl in dataset[0:no_of_rows]:
        tupl[column_idx] = tupl[column_idx] + 1000
    # pollute back
    for tupl in dataset[-no_of_rows:]:
        tupl[column_idx] = 0
    return dataset
    
def main():
    filename = 'pima-indians-diabetes.csv'
    splitRatio = 0.67
    dataset = loadCsv(filename)
    
    trainingSet, testSet = splitDataset(dataset, splitRatio)
    print('Split {0} rows into train = {1} and test = {2} rows'.format(len(dataset),len(trainingSet),len(testSet)))
    #prepare model
    summaries = summarizeByClass(trainingSet)
    #test model
    predictions = getPredictions(summaries, testSet)
    accuracy = getAccuracy(testSet, predictions)
    print('Accuracy: {0}%'.format(accuracy))

    # attacks:
    polluted_0 = pollute(dataset, 0, 77)
    #print(polluted_0)
    polluted_1 = pollute(dataset, 1, 77)
    polluted_2 = pollute(dataset, 2, 77)
    polluted_3 = pollute(dataset, 3, 77)
    polluted_4 = pollute(dataset, 4, 77)
    polluted_5 = pollute(dataset, 5, 77)
    polluted_6 = pollute(dataset, 6, 77)
    polluted_7 = pollute(dataset, 7, 77)
    
    # attacked column 0
    trainingSet_0, testSet_0 = splitDataset(polluted_0, splitRatio)
    summaries_0 = summarizeByClass(trainingSet_0)
    predictions_0 = getPredictions(summaries_0, testSet_0)
    accuracy_0 = getAccuracy(testSet_0, predictions_0)
    print('Accuracy_0: {0}%'.format(accuracy_0))

    # attacked column 1
    trainingSet_1, testSet_1 = splitDataset(polluted_1, splitRatio)
    summaries_1 = summarizeByClass(trainingSet_1)
    predictions_1 = getPredictions(summaries_1, testSet_1)
    accuracy_1 = getAccuracy(testSet_1, predictions_1)
    print('Accuracy_1: {0}%'.format(accuracy_1))

    # attacked column 2
    trainingSet_2, testSet_2 = splitDataset(polluted_2, splitRatio)
    summaries_2 = summarizeByClass(trainingSet_2)
    predictions_2 = getPredictions(summaries_2, testSet_2)
    accuracy_2 = getAccuracy(testSet_2, predictions_2)
    print('Accuracy_2: {0}%'.format(accuracy_2))

    # attacked column 3
    trainingSet_3, testSet_3 = splitDataset(polluted_3, splitRatio)
    summaries_3 = summarizeByClass(trainingSet_3)
    predictions_3 = getPredictions(summaries_3, testSet_3)
    accuracy_3 = getAccuracy(testSet_3, predictions_3)
    print('Accuracy_3: {0}%'.format(accuracy_3))

    # attacked column 4
    trainingSet_4, testSet_4 = splitDataset(polluted_4, splitRatio)
    summaries_4 = summarizeByClass(trainingSet_4)
    predictions_4 = getPredictions(summaries_4, testSet_4)
    accuracy_4 = getAccuracy(testSet_4, predictions_4)
    print('Accuracy_4: {0}%'.format(accuracy_4))

    # attacked column 5
    trainingSet_5, testSet_5 = splitDataset(polluted_5, splitRatio)
    summaries_5 = summarizeByClass(trainingSet_5)
    predictions_5 = getPredictions(summaries_5, testSet_5)
    accuracy_5 = getAccuracy(testSet_5, predictions_5)
    print('Accuracy_5: {0}%'.format(accuracy_5))

    # attacked column 6
    trainingSet_6, testSet_6 = splitDataset(polluted_6, splitRatio)
    summaries_6 = summarizeByClass(trainingSet_6)
    predictions_6 = getPredictions(summaries_6, testSet_6)
    accuracy_6 = getAccuracy(testSet_6, predictions_6)
    print('Accuracy_6: {0}%'.format(accuracy_6))

    # attacked column 7
    trainingSet_7, testSet_7 = splitDataset(polluted_7, splitRatio)
    summaries_7 = summarizeByClass(trainingSet_7)
    predictions_7 = getPredictions(summaries_7, testSet_7)
    accuracy_7 = getAccuracy(testSet_7, predictions_7)
    print('Accuracy_7: {0}%'.format(accuracy_7))



 
main()