package pea_to_boogie.generator;

import java.util.ArrayList;
import java.util.List;

public class Permutation {
    public  List<List<Integer>> allPermutations(List<List<Integer>> input, int counter) {   	
    	if (input.size() == 1) return input;
    	if (counter == input.size()) { 
        	List<List<Integer>> result = new ArrayList<List<Integer>>();
        	for (int i = 0; i < input.get(counter-1).size(); i++) {
        		List<Integer> tempList = new ArrayList<Integer>();
        		tempList.add(input.get(counter-1).get(i));
        		result.add(tempList);
        	}       	
        	return result;
        }
    	List<List<Integer>> myListList = new ArrayList<List<Integer>>();
        for (int i = 0; i < input.get(counter - 1).size(); i++) {      	
    	    myListList = permutConcat(myListList, input.get(counter - 1).get(i), allPermutations(input, counter + 1));
        }  
    	return myListList;
    }
    public List<List<Integer>> permutation(List<Integer> myList, int combinationNum) {   	
    	if (combinationNum == 1) { 
        	List<List<Integer>> result = new ArrayList<List<Integer>>();
        	for (int i = 0; i < myList.size(); i++) {
        		List<Integer> tempList = new ArrayList<Integer>();
        		tempList.add(myList.get(i));
        		result.add(tempList);
        	}
        	return result;
        }
    	List<List<Integer>> myListList = new ArrayList<List<Integer>>();
        for (int i = 0; i <= myList.size() - combinationNum; i++) {      	
    	    myListList = permutConcat(myListList, myList.get(i), permutation(skipElements(myList, i + 1), combinationNum - 1));
        }  
    	return myListList;
    }
    public List<List<Integer>> permutConcat(List<List<Integer>> result, Integer integer, List<List<Integer>> myListList) {
    	for(int i = 0; i < myListList.size(); i++){
    		List<Integer> innerList = myListList.get(i);
            innerList.add(integer);
    		result.add(innerList);
    	}
    	return result;
    }
    public List<Integer> skipElements(List<Integer> myList, int skipNum) {
    	List<Integer> result = new ArrayList<Integer>();
    	for(int i = skipNum; i < myList.size(); i++) {
    		result.add(myList.get(i));
    	}
    	return result; 
    }
}
