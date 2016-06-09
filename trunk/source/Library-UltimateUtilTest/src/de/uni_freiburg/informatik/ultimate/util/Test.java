/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Util Library.
 * 
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Util Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.util.statistics.Benchmark;

public class Test {

	public static void main(String[] args) throws InterruptedException {
// compare HashMap with LinkedHashMap
		
		final int count = 3000000;
		
		final HashMap<String, String> useless = new HashMap<>(count);
		
		final HashMap<String, String> hashmap = new HashMap<>();
		final LinkedHashMap<String, String> linkedHashMap = new LinkedHashMap<>();
		
		final ArrayList<String> input = new ArrayList<>();
		

		for(int i=0;i<count;i++){
			input.add("The string no "+i);
		}
		
		for(final String s : input){
			useless.put(s, s);
		}
		
		final Benchmark bench = new Benchmark();
		
		Thread.sleep(100);
		

		
		bench.start("HashMap.put()");
		for(final String s : input){
			hashmap.put(s, s);
		}
		bench.stop("HashMap.put()");
		
		System.gc();
		
		bench.start("LinkedHashMap.put()");
		for(final String s : input){
			linkedHashMap.put(s, s);
		}
		bench.stop("LinkedHashMap.put()");
		System.gc();
		
		boolean x = false;
		bench.start("HashMap.contains()");
		for(final String s : input){
			x = x && hashmap.containsKey(s);
		}
		bench.stop("HashMap.contains()");
		System.gc();
		
		bench.start("LinkedHashMap.contains()");
		for(final String s : input){
			x = x && linkedHashMap.containsKey(s);
		}
		bench.stop("LinkedHashMap.contains()");
		

		useless.clear();
		System.gc();
		
		bench.start("HashMap.values()");
		for(final String s : hashmap.values()){
			useless.put(s, s);
		}
		bench.stop("HashMap.values()");
		
		
		useless.clear();
		System.gc();
		
		bench.start("LinkedHashMap.values()");
		for(final String s : linkedHashMap.values()){
			useless.put(s, s);
		}
		bench.stop("LinkedHashMap.values()");

		useless.clear();
		System.gc();
		
		bench.start("HashMap.keySet()");
		for(final String s : hashmap.keySet()){
			useless.put(s, s);
		}
		bench.stop("HashMap.keySet()");
		
		useless.clear();
		System.gc();
		
		bench.start("LinkedHashMap.keySet()");
		for(final String s : linkedHashMap.keySet()){
			useless.put(s, s);
		}
		bench.stop("LinkedHashMap.keySet()");
		
		useless.clear();
		System.gc();
		
		bench.start("HashMap.get()");
		for(final String s : input){
			useless.put(s, hashmap.get(s));
		}
		bench.stop("HashMap.get()");
		
		useless.clear();
		System.gc();
		
		bench.start("LinkedHashMap.get()");
		for(final String s : input){
			useless.put(s, linkedHashMap.get(s));
		}
		bench.stop("LinkedHashMap.get()");
		
		useless.clear();
		System.gc();
		
		bench.start("HashMap.remove()");
		for(final String s : input){
			hashmap.remove(s);
		}
		bench.stop("HashMap.remove()");
		
		System.gc();
		
		bench.start("LinkedHashMap.remove()");
		for(final String s : input){
			linkedHashMap.remove(s);
		}
		bench.stop("LinkedHashMap.remove()");
		
		System.gc();
		
		
		final List<String> titles = bench.getTitles();
		Collections.sort(titles);		
		
		for(final String s : titles){
			System.out.println(bench.getReportString(s));
		}
	}

}
