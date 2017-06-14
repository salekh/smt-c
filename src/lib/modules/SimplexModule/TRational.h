/**
 * @file TRational.h
 * @author Sanchit Alekh <sanchit.alekh@rwth-aachen.de>
 * @author Karsten Jungnitsch <karsten.jungnitsch@rwth-aachen.de>
 * @author Alexander Reeh <alexander.reeh@rwth-aachen.de>
 *
 */

#include <stack>
#include "../../Common.h"
#include "Bound.h"
#include <limits>

namespace smtrat 

class TRational
{

private:
	/**
	* Rational Part (for weak inequalities)
	*/
	Rational rationalValue;

	/*
	* Delta Part (for strict inequalities)
	*/	
	Rational deltaValue;

public:
	
	/*
	* getter for Rational Value
	* @return Rational Value
	*/
	Rational getRationalValue();

	
	/*
	* getter for Delta Value
	* @return Delta Value
	*/

	Rational getDeltaValue();

		
	/****************************************
	OVERLOADING THE COMPARISON OPERATORS 
	******************************************/

	/**
     * 
     * @param _value
     * @return
     */
	TRational& operator=(const TRational& _value);

	/**
     * 
     * @param _value
     * @return
     */
	TRational operator +( const TRational& _value) const;

	/**
     * 
     * @param _value
     */
	void operator +=( const TRational& _value );

	
	/**
     * @param _value
     * @return
     */
	TRational operator -( const TRational& _value ) const;

	/**
     * 
     * @param _value
     */
	void operator -=( const TRational& _value );

	/**
     * 
     * @param _a
     * @return
     */
	TRational operator *( const Rational& _a ) const;

	/**
     * 
     * @param _value
     */
	void operator *=( const Value<T>& _value );
                
    /**
     * 
     * @param _a
     */
     void operator *=( const Rational& _a );

    /**
     * 
     * @param _a
     * @return 
     */
     TRational operator /( const Rational& _a ) const;

    /**
     * 
     * @param _a
     */
     void operator /=( const Rational& _a );

    /**
     * 
     * @param _value
     * @return 
     */
     bool operator <( const TRational& _value ) const;
     bool operator >( const TRational& _value ) const
     {
     	return _value < *this;
     }

    /**
     * 
     * @param _value
     * @return 
     */
     bool operator <=( const TRational& _value ) const;
     bool operator >=( const TRational& _value ) const
     {
     	return _value <= *this;
     }

    /**
     * 
     * @param _value
     * @return 
     */
     bool operator ==( const TRational& _value ) const;
     bool operator !=( const TRational& _value ) const
     {
     	return !(*this == _value);
     }

    /**
     * 
     * @param _a
     * @return 
     */
     bool operator ==( const Rational& _a ) const;
     bool operator !=( const Rational& _a ) const
     {
     	return !(*this == _a);
     }

    /**
     * 
     * @param _a
     * @return 
     */
     bool operator <( const Rational& _a ) const;

    /**
     * 
     * @param _a
     * @return 
     */
     bool operator >( const Rational& _a ) const;

    /**
     * 
     * @param _a
     * @return 
     */
     bool operator <=( const Rational& _a ) const;

    /**
     * 
     * @param _a
     * @return 
     */
     bool operator >=( const Rational& _a ) const;
	/*
	*
	*/
	TRational(const Rational& rationalPart, const Rational& deltaPart);
	
	/*
	*
	*/
	TRational(const Rational& rationalPart);
	
	/*
	* Default constructor
	*/
	TRational();
	

	virtual ~TRational();
	
};
