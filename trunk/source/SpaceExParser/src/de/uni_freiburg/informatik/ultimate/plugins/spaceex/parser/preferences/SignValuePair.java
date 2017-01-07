package de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.preferences;

public class SignValuePair {
	String mSign;
	String mValue;
	
	public SignValuePair(String sign, String value) {
		mSign = sign;
		mValue = value;
	}
	
	public String getSign() {
		return mSign;
	}
	
	public String getValue() {
		return mValue;
	}
	
	@Override
	public String toString() {
		return "(" + mSign + ", " + mValue + ")";
	}
}
