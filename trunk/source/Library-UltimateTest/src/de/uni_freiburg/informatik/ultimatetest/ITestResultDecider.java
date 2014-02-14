package de.uni_freiburg.informatik.ultimatetest;

public interface ITestResultDecider {
	public boolean isResultFail();
	public boolean isResultFail(Exception e);
	
}
