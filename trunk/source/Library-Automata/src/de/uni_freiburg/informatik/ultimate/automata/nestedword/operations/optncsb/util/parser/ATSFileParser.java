package util.parser;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import automata.IBuchi;
import util.PairXX;


// now we only support ATS format of Ultimate tools
// every automaton in the same file share the SAME alphabets

public class ATSFileParser {
	
	private List<String> mAlphabets;
	private List<PairXX<IBuchi>> mBuchiPairs;
	
	private Map<String, Integer> mAlphabetMap;
	private Map<String, Integer> mStateMap;
	
	
	public ATSFileParser() {
		this.mAlphabets = new ArrayList<>();
		this.mBuchiPairs = new ArrayList<>();
		this.mAlphabetMap = new HashMap<>();
		this.mStateMap = new HashMap<>();
	}
	
	public void addPair(PairXX<IBuchi> pair) {
		mBuchiPairs.add(pair);
	}
	
	public void addPair(IBuchi fstBuchi, IBuchi sndBuchi) {
		mBuchiPairs.add(new PairXX<IBuchi>(fstBuchi, sndBuchi));
	}
	
	public void setAlphabet(List<String> alphabet) {
		mAlphabets = alphabet;
	}
	
	public List<String> getAlphabet() {
		return Collections.unmodifiableList(mAlphabets);
	}
	
	public int getLetterId(String letterStr) {
		return mAlphabetMap.get(letterStr);
	}
	
	public int getStateId(String stateStr) {
		return mStateMap.get(stateStr);
	}
	
	public void clearStateMap() {
		mStateMap.clear();
	}
	
	public void addLetter(String letterStr) {
		if(! mAlphabetMap.containsKey(letterStr)) {
			mAlphabetMap.put(letterStr, mAlphabets.size());
			mAlphabets.add(letterStr);
		}
	}
	
	public int getAlphabetSize() {
		return mAlphabets.size();
	}
	
	// not necessary
//	public void clearAlphabetMap() {
//		mAlphabetMap.clear();;
//	}
	
//	public void putLetter(String letterStr, int letter) {
//		mAlphabetMap.put(letterStr, letter);
//	}
	
	public void putState(String stateStr, int state) {
		mStateMap.put(stateStr, state);
	}
	
	public List<PairXX<IBuchi>> getBuchiPairs() {
		return Collections.unmodifiableList(mBuchiPairs);
	}
	
	public void parse(String file) {
		try {
			FileInputStream inputStream = new FileInputStream(new File(file));
			ATSParser parser = new ATSParser(inputStream);
			parser.parse(this);
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}
	}
	
	

}
