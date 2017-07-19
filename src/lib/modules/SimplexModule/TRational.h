/**
 * @file TRational.h
 * @author Sanchit Alekh <sanchit.alekh@rwth-aachen.de>
 * @author Karsten Jungnitsch <karsten.jungnitsch@rwth-aachen.de>
 * @author Alexander Reeh <alexander.reeh@rwth-aachen.de>
 *
 */

 #pragma once

#include "../../Common.h"
#include <sstream>

namespace smtrat{

	class TRational
	{

	private:
		/**
		* Rational Part (for weak inequalities)
		*/
		Rational rationalPart=0;

		/*
		* Delta Part (for strict inequalities)
		*/	
		Rational deltaPart=0;

		/*
		* Infinity part (1 = +inf, -1 = -inf, 0 != -/+ inf)
		*/

		Rational infPart = 0;

		/*
		* Boolean Value if Upper or Lower Bound
		*/

		bool upperBound;

	public:
		
		/*
		*
		*/
		TRational(const Rational& rational, const Rational& delta, const Rational& inf, bool bound);
		
		/*
		*
		*/
		
		
		TRational(const Rational& rational, const Rational& inf, bool bound);

		TRational(const Rational& rational);
		
		/*
		* Default constructor
		*/
		TRational();
		

		~TRational();

		/**************************************
					GETTERS
		**************************************/


		/*
		* getter for Rational Value
		* @return Rational Value
		*/
		const Rational& getRationalPart() const{
			return rationalPart;
		}

		
		/*
		* getter for Delta Value
		* @return Delta Value
		*/

		const Rational& getDeltaPart() const{
			return deltaPart;
		}

		/*
		* getter for Inf value
		*/

		const Rational& getInfPart() const{
			return infPart;
		}

		bool isUpperBound() const {
			return upperBound;
		}


		/****************************************
				OVERLOADING THE OPERATORS 
		******************************************/

		/**
		* 
		* Method for checking Inf
		* 
		*/

		Rational checkInf(const TRational& _a, const TRational& _b);

		/**
	     * 
	     * @param _rational
	     * @return
	     */
		TRational& operator=(const TRational& _rational);

		/**
	     * 
	     * @param _rational
	     * @return
	     */
		TRational operator +( const TRational& _rational) const;

		/**
	     * 
	     * @param _rational
	     */
		void operator +=( const TRational& _rational );


		/**
	     * @param _rational
	     * @return
	     */
		TRational operator -( const TRational& _rational ) const;

		/**
	     * 
	     * @param _rational
	     */
		void operator -=( const TRational& _rational );

		/**
	     * 
	     * @param _a
	     * @return
	     */
		TRational operator *( const Rational& _a ) const;

		/**
	     * 
	     * @param _rational
	     */
		void operator *=( const TRational& _rational );

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
	     * @param _rational
	     * @return 
	     */
		bool operator <( const TRational& _rational ) const;
		bool operator >( const TRational& _rational ) const
		{
			return _rational < *this;
		}

	    /**
	     * 
	     * @param _rational
	     * @return 
	     */
		bool operator <=( const TRational& _rational ) const;
		bool operator >=( const TRational& _rational ) const
		{
			return _rational <= *this;
		}

	    /**
	     * 
	     * @param _rational
	     * @return 
	     */
		bool operator ==( const TRational& _rational ) const;
		bool operator !=( const TRational& _rational ) const
		{
			return !(*this == _rational);
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

		
		friend std::ostream& operator<<( std::ostream& stream, const TRational& t );
	};



}