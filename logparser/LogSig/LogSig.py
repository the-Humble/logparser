"""
Description : This file implements the LogSig algorithm for log parsing
Author      : LogPAI team
License     : MIT
"""

from datetime import datetime
import random
import math
import time
import operator
import re
import os
import pandas as pd
import hashlib

#<comentario> Parametros de parseo
class Para:
    def __init__(self, path, rex, savePath, groupNum, logformat): 
        self.path = path
        self.rex = rex #<comentario> expresion regular
        self.savePath = savePath
        self.groupNum = groupNum  # partition into k groups
        self.logformat = logformat

#<comentario> Parseador/analizador
class LogParser:
    #<comentario> constructtor
    def __init__(self, indir, outdir, groupNum, log_format, rex=[], seed=0):

        self.para = Para(path=indir, rex=rex, savePath=outdir, groupNum=groupNum, logformat=log_format) #<comentario> paaramettros
        self.wordLL = [] #<comentario> lista de listtas de palabras
        self.loglineNum = 0
        self.termpairLLT = [] #<comentario> lista de listas de parejas termino- posicion
        self.logNumPerGroup = [] #<comentario> numero de logs por grupo
        self.groupIndex = dict()  # each line corresponding to which group
        self.termPairLogNumLD = []
        self.logIndexPerGroup = []
        self.seed = seed

    #<comentario> carga el dataset y usa expresiones regulares para separar los logs y remover columnas
    def loadLog(self):
        """ Load datasets and use regular expression to split it and remove some columns 
        """
        print('Loading logs...')
        headers, regex = self.generate_logformat_regex(self.para.logformat)
        self.df_log = self.log_to_dataframe(os.path.join(self.para.path, self.logname), regex, headers,
                                            self.para.logformat)
        #<comentario> pasa los logs a tabla y por cada linea de la tabla checa las expresiones regulares en los parametros substituyendo los matches por caracteres vacios
        #y convierte el log a una listta que se agrega a otra lista
        for idx, line in self.df_log.iterrows():
            line = line['Content']
            if self.para.rex:
                for currentRex in self.para.rex:
                    line = re.sub(currentRex, '', line)

            wordSeq = line.strip().split()
            self.wordLL.append(tuple(wordSeq))

    #<comentario> genera los pares de palabras para agregarlos a la lista termpairLLt donnde cada elemento es una lista de pares por log verifcando aquellos
    #que contegan el caracter $ en ellos
    #los divide en grupos aleatorios y cuentta la frecuencia de cada par en los grupos
    def termpairGene(self):
        print('Generating term pairs...')
        i = 0
        for wordL in self.wordLL:
            wordLT = []
            for j in range(len(wordL)):
                for k in range(j + 1, len(wordL), 1):
                    if wordL[j] != '[$]' and wordL[k] != '[$]':
                        termpair = (wordL[j], wordL[k])
                        wordLT.append(termpair)
            self.termpairLLT.append(wordLT)
            i += 1

        # termPairLogNumLD, used to account the occurrence of each termpair of each group
        for i in range(self.para.groupNum):
            newDict = dict()
            self.termPairLogNumLD.append(newDict)
            # initialize the item value to zero
            self.logNumPerGroup.append(0)

        # divide logs into initial groupNum groups randomly, the group number of each log is stored in the groupIndex
        self.loglineNum = len(self.wordLL)
        random.seed(self.seed)
        for i in range(self.loglineNum):
            ran = random.randint(0, self.para.groupNum - 1)  # group number from 0 to k-1
            self.groupIndex[i] = ran
            self.logNumPerGroup[ran] += 1  # count the number of loglines per group

        # count the frequency of each termpairs per group
        i = 0
        for termpairLT in self.termpairLLT:
            j = 0
            for key in termpairLT:
                currGroupIndex = self.groupIndex[i]
                if key not in self.termPairLogNumLD[currGroupIndex]:
                    self.termPairLogNumLD[currGroupIndex][key] = 1
                else:
                    self.termPairLogNumLD[currGroupIndex][key] += 1
                j += 1
            i += 1

    #<comentario> genera un posible nuevo grupo para una lista de pareja y si son diferenttes al actual se cambia el grupo y se ajustan los contteos de frecuencias
    def LogMessParti(self):
        """ Use local search, for each log, find the group that it should be moved to.
            in this process, termpairs occurange should also make some changes and logNumber 
            of corresponding should be changed
        """
        print('Log message partitioning...')
        changed = True
        while changed:
            changed = False
            i = 0
            for termpairLT in self.termpairLLT:
                curGroup = self.groupIndex[i]
                alterGroup = potenFunc(curGroup, self.termPairLogNumLD, self.logNumPerGroup, i, termpairLT,
                                       self.para.groupNum)
                if curGroup != alterGroup:
                    changed = True
                    self.groupIndex[i] = alterGroup
                    # update the dictionary of each group
                    for key in termpairLT:
                        # minus 1 from the current group count on this key
                        self.termPairLogNumLD[curGroup][key] -= 1
                        if self.termPairLogNumLD[curGroup][key] == 0:
                            del self.termPairLogNumLD[curGroup][key]
                        # add 1 to the alter group
                        if key not in self.termPairLogNumLD[alterGroup]:
                            self.termPairLogNumLD[alterGroup][key] = 1
                        else:
                            self.termPairLogNumLD[alterGroup][key] += 1
                    self.logNumPerGroup[curGroup] -= 1
                    self.logNumPerGroup[alterGroup] += 1
                i += 1

    #<comentario> define la signature que busca palabras candidatas a ser parte de los templates
    def signatConstr(self):
        """ Calculate the occurancy of each word of each group, and for each group, save the words that
            happen more than half all log number to be candidateTerms(list of dict, words:frequency),
        """
        print('Log message signature construction...')
        # create the folder to save the resulted templates
        if not os.path.exists(self.para.savePath):
            os.makedirs(self.para.savePath)

        wordFreqPerGroup = []
        candidateTerm = []
        candidateSeq = []
        self.signature = []

        # save the all the log indexs of each group: logIndexPerGroup
        for t in range(self.para.groupNum):
            dic = dict()
            newlogIndex = []
            newCandidate = dict()
            wordFreqPerGroup.append(dic)
            self.logIndexPerGroup.append(newlogIndex)
            candidateSeq.append(newCandidate)

        # count the occurence of each word of each log per group
        # and save into the wordFreqPerGroup, which is a list of dictionary,
        # where each dictionary represents a group, key is the word, value is the occurence
        lineNo = 0
        for wordL in self.wordLL:
            groupIndex = self.groupIndex[lineNo]
            self.logIndexPerGroup[groupIndex].append(lineNo)
            for key in wordL:
                if key not in wordFreqPerGroup[groupIndex]:
                    wordFreqPerGroup[groupIndex][key] = 1
                else:
                    wordFreqPerGroup[groupIndex][key] += 1
            lineNo += 1

        # calculate the halfLogNum and select those words whose occurence is larger than halfLogNum
        # as constant part and save into candidateTerm
        for i in range(self.para.groupNum):
            halfLogNum = math.ceil(self.logNumPerGroup[i] / 2.0)
            dic = dict((k, v) for k, v in wordFreqPerGroup[i].items() if v >= halfLogNum)
            candidateTerm.append(dic)

        # scan each logline's each word that also is a part of candidateTerm, put these words together
        # as a new candidate sequence, thus, each raw log will have a corresponding candidate sequence
        # and count the occurence of these candidate sequence of each group and select the most frequent
        # candidate sequence as the signature, i.e. the templates
        lineNo = 0
        for wordL in self.wordLL:
            curGroup = self.groupIndex[lineNo]
            newCandiSeq = []

            for key in wordL:
                if key in candidateTerm[curGroup]:
                    newCandiSeq.append(key)

            keySeq = tuple(newCandiSeq)
            if keySeq not in candidateSeq[curGroup]:
                candidateSeq[curGroup][keySeq] = 1
            else:
                candidateSeq[curGroup][keySeq] += 1
            lineNo += 1

        for i in range(self.para.groupNum):
            sig = max(candidateSeq[i].items(), key=operator.itemgetter(1))[0]
            self.signature.append(sig)

    #<comentario> 
    def writeResultToFile(self):
        idx_eventID = {} #<comentario> diccionario para los hash de las firmas
        for idx, item in enumerate(self.signature): #<comentario> por cada indice y elemento
            eventStr = ' '.join(item) #<comentario> une la firma en un solo string
            idx_eventID[idx] = hashlib.md5(eventStr.encode('utf-8')).hexdigest()[0:8] #<comentario> agrega en el numero de grupo (o de lista) los primeros 8 caracteres
            #del hash de la firma

        EventId = []
        EventTemplate = []
        LineId_groupId = [] #<comentario> Lista de pares (# de elemento en la lista, # de lista)
        for idx, item in enumerate(self.logIndexPerGroup):
            for LineId in item:
                LineId_groupId.append([LineId, idx])
        LineId_groupId.sort(key=lambda x:x[0])
        for item in LineId_groupId:
            GroupID = item[1] #<comentario> numero dee lista
            EventId.append(idx_eventID[GroupID])
            EventTemplate.append(' '.join(self.signature[GroupID])) #<comentario> agragas el ttemplate uniendo las firmas de un grupo

        #<comentario> creacion del csv de templates y elementtos
        self.df_log['EventId'] = EventId
        self.df_log['EventTemplate'] = EventTemplate
        self.df_log.to_csv(os.path.join(self.para.savePath, self.logname + '_structured.csv'), index=False)


        occ_dict = dict(self.df_log['EventTemplate'].value_counts()) #<comentario> diccionario de ocuurencias de los ttemplates
        df_event = pd.DataFrame()
        df_event['EventTemplate'] = self.df_log['EventTemplate'].unique() #<comentario> templates unicos
        df_event['EventId'] = df_event['EventTemplate'].map(lambda x: hashlib.md5(x.encode('utf-8')).hexdigest()[0:8]) #<comentario> hash de los templates
        df_event['Occurrences'] = df_event['EventTemplate'].map(occ_dict) #<comentario> ocurrencias de los ttemplattes
        #<comentario> csv de ttemplates
        df_event.to_csv(os.path.join(self.para.savePath, self.logname + '_templates.csv'), index=False, columns=["EventId", "EventTemplate","Occurrences"])

    #<comentario> convierte los logs a una tabla que busca el match con expresiones regulares y especifica en quee linea aparecen
    def log_to_dataframe(self, log_file, regex, headers, logformat):
        """ Function to transform log file to dataframe """
        log_messages = []
        linecount = 0
        with open(log_file, 'r') as fin:
            for line in fin.readlines():
                try:
                    match = regex.search(line.strip())
                    message = [match.group(header) for header in headers]
                    log_messages.append(message)
                    linecount += 1
                except Exception as e:
                    pass
        logdf = pd.DataFrame(log_messages, columns=headers)
        logdf.insert(0, 'LineId', None)
        logdf['LineId'] = [i + 1 for i in range(linecount)]
        return logdf

    #<comentario> genera las expresiones regulares y los encabezados en base al formato
    def generate_logformat_regex(self, logformat):
        """ 
        Function to generate regular expression to split log messages
        """
        headers = []
        splitters = re.split(r'(<[^<>]+>)', logformat) #<comentario> busca que el formato sean expresiones entre <>
        regex = ''
        for k in range(len(splitters)):
            if k % 2 == 0:
                splitter = re.sub(' +', '\\\s+', splitters[k]) #<comentario> cambia los espacios por espacios en blanco (por ejemplo tabuladores o saltos de linea)
                regex += splitter
            else:
                header = splitters[k].strip('<').strip('>')
                regex += '(?P<%s>.*?)' % header
                headers.append(header)
        regex = re.compile('^' + regex + '$')
        return headers, regex

    #<comentario> manda a llamar todas las funciones para el parseo
    def parse(self, logname):
        print('Parsing file: ' + os.path.join(self.para.path, logname))
        start_time = datetime.now()
        self.logname = logname
        self.loadLog()
        self.termpairGene()
        self.LogMessParti()
        self.signatConstr()
        self.writeResultToFile()
        print('Parsing done. [Time taken: {!s}]'.format(datetime.now() - start_time))

#<comentario> determina el potencial de una frase a ser parte de un ttemplate
def potenFunc(curGroupIndex, termPairLogNumLD, logNumPerGroup, lineNum, termpairLT, k):
    maxDeltaD = 0
    maxJ = curGroupIndex
    for i in range(k):
        returnedDeltaD = getDeltaD(logNumPerGroup, termPairLogNumLD, curGroupIndex, i, lineNum, termpairLT)
        if returnedDeltaD > maxDeltaD:
            maxDeltaD = returnedDeltaD
            maxJ = i
    return maxJ


# part of the potential function
def getDeltaD(logNumPerGroup, termPairLogNumLD, groupI, groupJ, lineNum, termpairLT):
    deltaD = 0
    Ci = logNumPerGroup[groupI]
    Cj = logNumPerGroup[groupJ]
    for r in termpairLT:
        if r in termPairLogNumLD[groupJ]:
            deltaD += (pow(((termPairLogNumLD[groupJ][r] + 1) / (Cj + 1.0)), 2) \
                       - pow((termPairLogNumLD[groupI][r] / (Ci + 0.0)), 2))
        else:
            deltaD += (pow((1 / (Cj + 1.0)), 2) - pow((termPairLogNumLD[groupI][r] / (Ci + 0.0)), 2))
    deltaD = deltaD * 3
    return deltaD

input_dir    = '../logs/HDFS/' # The input directory of log file
output_dir   = 'LogSig_result/' # The output directory of parsing results
log_file     = 'HDFS_2k.log' # The input log file name
log_format   = '<Date> <Time> <Pid> <Level> <Component>: <Content>' # HDFS log format
regex        = []  # Regular expression list for optional preprocessing (default: [])
group_number = 14 # The number of message groups to partition

parser = LogParser(input_dir, output_dir, group_number, log_format, rex=regex)
parser.parse(log_file)
