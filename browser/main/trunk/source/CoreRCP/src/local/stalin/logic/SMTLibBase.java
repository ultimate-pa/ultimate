package local.stalin.logic;

import java.io.Serializable;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;

public abstract class SMTLibBase implements Serializable {
	private static final long serialVersionUID = -2333489226895351545L;
	private HashMap<String,String> annotations;

	public abstract boolean typeCheck();
	
	public void setAnnotations(HashMap<String,String> annotations) {
		this.annotations = annotations;
	}
	public void addAnnotation(String key, String value) {
		if (annotations == null)
			annotations = new HashMap<String,String>();
		annotations.put(key, value);
	}
	
	protected String getStringOfAnnotations() {
		if (annotations == null)
			return "";
		StringBuilder sb = new StringBuilder();
		for (Entry<String,String> e : annotations.entrySet()) {
			sb.append(" :").append(e.getKey());
			if (e.getValue() != null) {
				sb.append(" {").append(e.getValue()).append("}");
			}
		}
		return sb.toString();
	}
	
	private static HashSet<String> keywords = new HashSet<String>();
	static {
		keywords.add("Int");
		keywords.add("select");
		keywords.add("store");
		keywords.add("ite");
		keywords.add("distinct");
		keywords.add("true");
		keywords.add("false");
		keywords.add("flet");
		keywords.add("forall");
		keywords.add("exists");
		keywords.add("and");
		keywords.add("or");
		keywords.add("xor");
		keywords.add("iff");
		keywords.add("implies");
		keywords.add("if_then_else");
		keywords.add("not");
		keywords.add("let");
		keywords.add("sat");
		keywords.add("unsat");
		keywords.add("unknown");
		keywords.add("theory");
		keywords.add("logic");
		keywords.add("benchmark");
	}

	/**
	 * Quote the given Id to only use characters allowed by smt-lib.
	 * We use ' as quotation symbol:
	 * <ul>
	 * <li>'' stands for $</li>
	 * <li>'_ stands for ! (used for internal purposes)</li>
	 * <li>'q stands for '</li>
	 * <li>'s stands for ~</li>
	 * <li>'h stands for #</li>
	 * <li>'x stands for ?</li>
	 * <li>'2ab' stands for unicode character 2ab (hex)</li>
	 * <li>letters, digits, underscore and dot are copied unquoted</li>
	 * <li>If id does not start with letter, x'. is prepended</li>
	 * </ul>
	 * @param id The id containing arbitrary characters.
	 * @return the id where all special characters are quoted.
	 */
	public static String quoteId(String id) {
		StringBuilder sb = new StringBuilder();
		char c = id.charAt(0); 
		for (int i = 0; i < id.length(); i++) {
			c = id.charAt(i);
			if ((c >= '0' && c <= '9') || (c >= 'A' && c <= 'Z') 
					|| (c >= 'a' && c <= 'z') || c == '.')
				sb.append(c);
			else if (c == '_')
				sb.append("__");
			else if (c == '\'')
				sb.append("_q");
			else if (c == '!')
				sb.append("_b");
			else if (c == '$')
				sb.append("_d");
			else if (c == '~')
				sb.append("_s");
			else if (c == '?')
				sb.append("_x");
			else if (c == '#')
				sb.append("_h");
			else
				sb.append('_').append(Integer.toHexString(c)).append('_');
		}
		return sb.toString();
	}
	/**
	 * Undoes a previous quotation with {@link #quoteId(String)}.
	 * 
	 * For each String s the equation
	 * <code>s.equals(unQuoteId(quoteId(s)))</code> holds.
	 * @param qid Quoted identifier as returned from {@link #quoteId(String)}.
	 * @return Original identifier.
	 */
	public static String unQuoteId(String qid) {
		StringBuilder sb = new StringBuilder();
		for (int i = 0; i < qid.length(); ++i) {
			char c = qid.charAt(i);
			if ((c >= '0' && c <= '9') || (c >= 'A' && c <= 'Z') 
					|| (c >= 'a' && c <= 'z') || c == '.')
				sb.append(c);
			else if (c == '_') {
				// Here we have a quoted symbol
				char symb = qid.charAt(++i);
				switch (symb) {
				case '_':
					sb.append('_');
					break;
				case 'q':
					sb.append('\'');
					break;
				case 'b':
					sb.append('!');
					break;
				case 'd':
					sb.append('$');
					break;
				case 's':
					sb.append('~');
					break;
				case 'x':
					sb.append('?');
					break;
				case 'h':
					sb.append('#');
					break;
				default:
					int endidx = qid.indexOf('_', i);
					if (endidx == -1)
						throw new IllegalArgumentException(
								"String is not correctly quoted");
					String hexstring = qid.substring(i, endidx);
					char hexchar;
					try {
						// Here, I assume char is always positive.
						hexchar = (char)Integer.parseInt(hexstring, 16);
					} catch (NumberFormatException nfe) {
						throw new IllegalArgumentException(
								"String is not correctly quoted",nfe);
					}
					sb.append(hexchar);
					i = endidx;
				}
			}
		}
		return sb.toString();
	}
}
