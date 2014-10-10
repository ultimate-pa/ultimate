package de.uni_freiburg.informatik.ultimate.model;

import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.model.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * A concrete implementation of the {@link IPayload} interface. The payload
 * contains all informations carried by a node.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class Payload implements IPayload {

	private static final long serialVersionUID = 9150283961581614549L;
	protected ILocation mLocation;
	protected String mName;
	protected UltimateUID mID;
	protected HashMap<String, IAnnotations> mAnnotations;
	protected boolean mIsValue;

	public Payload() {
		mIsValue = false;
	}

	public Payload(ILocation loc, String name) {
		this();
		mLocation = loc;
		mName = name;
	}

	public Payload(ILocation loc, String name, boolean isValue) {
		this();
		mLocation = loc;
		mName = name;
		mIsValue = isValue;
	}

	public HashMap<String, IAnnotations> getAnnotations() {
		if (mAnnotations == null) {
			mAnnotations = new HashMap<String, IAnnotations>();
		}
		return mAnnotations;
	}

	public UltimateUID getID() {
		if (mID == null) {
			mID = new UltimateUID();
		}
		return mID;
	}

	public ILocation getLocation() {
		return mLocation;
	}

	public String getName() {
		if (mName == null) {
			return "";
		}
		return mName;
	}

	public void setAnnotations(HashMap<String, IAnnotations> annotations) {
		mAnnotations = annotations;

	}

	public void setLocation(ILocation loc) {
		mLocation = loc;
	}

	public void setName(String name) {
		mName = name;
	}

	public String toString() {
		return getName();
	}

	public boolean hasAnnotation() {
		if (mAnnotations == null) {
			return false;
		}
		return !mAnnotations.isEmpty();
	}

	public boolean hasLocation() {
		return (mLocation != null);
	}

	public boolean hasID() {
		return (mID != null);
	}

	public boolean hasName() {
		return (mName != null);
	}

	public boolean isValue() {
		return mIsValue;
	}

}
