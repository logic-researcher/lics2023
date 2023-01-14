package tool;

import org.junit.Test;

import java.io.*;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class Statistic {

    public static void analyzeMultiThreadExp() throws IOException {
        String logPath = "./log/output.log";
        String line;
        int single, multi;
        Long[] singleTime = new Long[]{0L, 0L}; //The first element represent Oxford
        Long[] multiTime = new Long[]{0L, 0L};
        String entailNum, partition;
        try(BufferedReader br = new BufferedReader(new FileReader(logPath));
            BufferedWriter bw = new BufferedWriter(new FileWriter("multiThreadExp.csv"))){
            bw.write("fileName, STime, MTime, timeRatio, partition, entailNum\n");
            while((line = br.readLine()) != null){
                int idx;
                if(line.contains("Oxford-ISG"))
                    idx = 1;
                else if(line.contains("BioPortal"))
                    idx = 0;
                else
                    continue;
                bw.write(line.substring(line.indexOf("-") + 2) + ",");
                br.readLine();
                line = br.readLine();
                if(line.contains("Single thread time consumption:")){
                    line = line.substring(line.indexOf(": ") + 2);
                    bw.write(line + ",");
                    single = Integer.parseInt(line);

                }else {
                    System.out.println("Unknown error!: " + line);
                    bw.write("\n");
                    continue;
                }
                line = br.readLine();
                if(line.contains("The size of hasChecked:")){
                    entailNum = line.substring(line.indexOf(": ") + 2);
                }else{
//                    System.out.println("Unknown error!");
                    System.out.println("Unknown error!: " + line);
                    bw.write("\n");
                    continue;
                }
                line = br.readLine();
                if(line.contains("Time out!")){
                    bw.write("Time out\n");
                    continue;
                }
                else if(line.contains("MaxPartition / ForgettingSignatures")){
                    partition = line.substring(line.indexOf(": ") + 2);
                    partition = partition.replaceAll(" ", "");
                    partition = partition.replace("/", "//");
                }else if(line.contains("There is extra expressivity")){
                    bw.write("Extra\n");
                    continue;
                }
                else{
                    System.out.println("Unknown error!: " + line);
                    bw.write("\n");
                    continue;
                }
                line = br.readLine();
                line = br.readLine();
                if(line.contains("Multi thread time consumption")){
                    line = line.substring(line.indexOf(": ") + 2);
                    bw.write(line + ",");
                    multi = Integer.parseInt(line);
                }else{
                    continue;
                }
                line = br.readLine();
                if(line.contains("ratio:")){
                    line = line.substring(line.indexOf(": ") + 2);
                    bw.write(line + ",");
                }
                bw.write(partition + "," + entailNum + "\n");
                singleTime[idx] += single;
                multiTime[idx] += multi;
            }

        }
        System.out.println("BioPortal: " + 1.0 * singleTime[0] / multiTime[0]);
        System.out.println("Oxford: " + 1.0 * singleTime[1] / multiTime[1]);

    }

    public static void analyzeDepthAndTimeout(String fileName) throws Exception {
        String line;
        String[] values;
        Set<String> ontologies = new HashSet<>();
        Integer[] dpNum = new Integer[]{0, 0, 0, 0, 0, 0};
        Integer[] ourTimeoutNum = new Integer[]{0, 0, 0, 0, 0, 0};
        Integer[] letheTimeoutNum = new Integer[]{0, 0, 0, 0, 0, 0};
        Map<String, Integer> mdpMap = new HashMap<>();
        Map<String, Integer> ourTimeoutMap = new HashMap<>();
        Map<String, Integer> letheTimeoutMap = new HashMap<>();
        try(BufferedReader br = new BufferedReader(new FileReader(fileName))){
            br.readLine();
            while((line = br.readLine()) != null){
                values = line.split(",");
                if(values[0].equals("0")){
                    if(mdpMap.get(values[1]) == null && !values[values.length - 1].equals("")){
                        mdpMap.put(values[1], Integer.parseInt(values[values.length - 1].substring(0, 1)));
                        ourTimeoutMap.put(values[1], Integer.parseInt(values[11]));
                    }
                }else if(values[0].equals("1")){
                    if(letheTimeoutMap.get(values[1]) == null){
                        letheTimeoutMap.put(values[1], Integer.parseInt(values[11]));
                    }
                }
                ontologies.add(values[1].substring(values[1].lastIndexOf("/") + 1));
            }
        }
        System.out.println("mdpMap size: " + mdpMap.size());
        for(String ontoName: mdpMap.keySet()){
            dpNum[mdpMap.get(ontoName) - 1]++;
            ourTimeoutNum[mdpMap.get(ontoName) - 1] += ourTimeoutMap.get(ontoName);
            letheTimeoutNum[mdpMap.get(ontoName) - 1] += letheTimeoutMap.get(ontoName);
        }
        for(int i = 0; i <= 6; i++){
            System.out.printf("%.2f ", 100.0 * dpNum[i] / mdpMap.size());
            System.out.print(i + 1);
            System.out.printf(" %.2f", 100.0 * letheTimeoutNum[i] / dpNum[i]);
            System.out.printf(" %.2f\n", 100.0 * ourTimeoutNum[i] / dpNum[i]);
        }

    }

    @Test
    public static void analyzeSnomedType() throws Exception{
        String filePath = "snomedType.txt";
//        int conceptNum = 0, conceptType1 = 0, conceptType2 = 0, conceptType3 = 0, conceptType4 = 0;
        int[] conceptNum = new int[]{0, 0, 0, 0, 0};
        Set<String> ontologies = new HashSet<>();
        try(BufferedReader br = new BufferedReader(new FileReader(filePath))){
            String line;
            String[] values;
            while((line = br.readLine()) != null){
                values = line.split("\\s+");
                if(values[0].equals("1")){
                    if(ontologies.add(values[2]))
                        for(int i = 0; i < 5; i++){
                            conceptNum[i] += Integer.parseInt(values[3 + i]);
                        }
                    values = br.readLine().split(" ");
                    String[] task = values[1].split(",");
                    String taskName = task[0].substring(task[0].lastIndexOf("_") + 1) + "-" +
                            task[1].substring(task[1].lastIndexOf("_") + 1);
//                    System.out.printf("%s: %.2f\n", taskName, 100.0 * Integer.parseInt(values[6]) / Integer.parseInt(values[2]));
                    System.out.printf("%.2f\n", 100.0 * Integer.parseInt(values[6]) / Integer.parseInt(values[2]));

                }
            }
        }
        System.out.println();
        for(int i = 0; i < 4; i++){
            System.out.printf("Type %d: %.2f%%\n", i+1, 100.0 * conceptNum[i + 1] / conceptNum[0]);
        }
    }

    public static void main(String[] args) throws Exception {
//        analyzeMultiThreadExp();
//        analyzeDepthAndTimeout("./OxfordAnalyse.csv");
//        analyzeDepthAndTimeout("./BioPortalAnalyse.csv");
        analyzeSnomedType();
    }
}
