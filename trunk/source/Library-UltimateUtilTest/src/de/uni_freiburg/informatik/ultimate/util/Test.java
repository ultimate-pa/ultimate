package de.uni_freiburg.informatik.ultimate.util;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;

public class Test {

	public static void main(String[] args) throws InterruptedException {
// compare HashMap with LinkedHashMap
		
		int count = 3000000;
		
		HashMap<String, String> useless = new HashMap<>(count);
		
		HashMap<String, String> hashmap = new HashMap<>();
		LinkedHashMap<String, String> linkedHashMap = new LinkedHashMap<>();
		
		ArrayList<String> input = new ArrayList<>();
		

		for(int i=0;i<count;i++){
			input.add("The string no "+i);
		}
		
		for(String s : input){
			useless.put(s, s);
		}
		
		Benchmark bench = new Benchmark();
		
		Thread.sleep(100);
		

		
		bench.start("HashMap.put()");
		for(String s : input){
			hashmap.put(s, s);
		}
		bench.stop("HashMap.put()");
		
		System.gc();
		
		bench.start("LinkedHashMap.put()");
		for(String s : input){
			linkedHashMap.put(s, s);
		}
		bench.stop("LinkedHashMap.put()");
		System.gc();
		
		boolean x = false;
		bench.start("HashMap.contains()");
		for(String s : input){
			x = x && hashmap.containsKey(s);
		}
		bench.stop("HashMap.contains()");
		System.gc();
		
		bench.start("LinkedHashMap.contains()");
		for(String s : input){
			x = x && linkedHashMap.containsKey(s);
		}
		bench.stop("LinkedHashMap.contains()");
		

		useless.clear();
		System.gc();
		
		bench.start("HashMap.values()");
		for(String s : hashmap.values()){
			useless.put(s, s);
		}
		bench.stop("HashMap.values()");
		
		
		useless.clear();
		System.gc();
		
		bench.start("LinkedHashMap.values()");
		for(String s : linkedHashMap.values()){
			useless.put(s, s);
		}
		bench.stop("LinkedHashMap.values()");

		useless.clear();
		System.gc();
		
		bench.start("HashMap.keySet()");
		for(String s : hashmap.keySet()){
			useless.put(s, s);
		}
		bench.stop("HashMap.keySet()");
		
		useless.clear();
		System.gc();
		
		bench.start("LinkedHashMap.keySet()");
		for(String s : linkedHashMap.keySet()){
			useless.put(s, s);
		}
		bench.stop("LinkedHashMap.keySet()");
		
		useless.clear();
		System.gc();
		
		bench.start("HashMap.get()");
		for(String s : input){
			useless.put(s, hashmap.get(s));
		}
		bench.stop("HashMap.get()");
		
		useless.clear();
		System.gc();
		
		bench.start("LinkedHashMap.get()");
		for(String s : input){
			useless.put(s, linkedHashMap.get(s));
		}
		bench.stop("LinkedHashMap.get()");
		
		useless.clear();
		System.gc();
		
		bench.start("HashMap.remove()");
		for(String s : input){
			hashmap.remove(s);
		}
		bench.stop("HashMap.remove()");
		
		System.gc();
		
		bench.start("LinkedHashMap.remove()");
		for(String s : input){
			linkedHashMap.remove(s);
		}
		bench.stop("LinkedHashMap.remove()");
		
		System.gc();
		
		
		List<String> titles = bench.getTitles();
		Collections.sort(titles);		
		
		for(String s : titles){
			System.out.println(bench.getReportString(s));
		}
	}

}
