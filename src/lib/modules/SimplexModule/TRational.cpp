/**
 * @file TRational.h
 * @author Sanchit Alekh <sanchit.alekh@rwth-aachen.de>
 * @author Karsten Jungnitsch <karsten.jungnitsch@rwth-aachen.de>
 * @author Alexander Reeh <alexander.reeh@rwth-aachen.de>
 *
 */

#pragma once

#include "TRational.h"

namespace smtrat {

	/**************************************
				CONSTRUCTORS
	**************************************/

	TRational::TRational():
		rationalPart(0),
		deltaPart(0)
	{}

	TRational::TRational(const Rational& rational):
		rationalPart(rational),
		deltaPart(0)
	{}

	TRational::TRational(const Rational& rational, const Rational& delta):
		rationalPart(rational),
		deltaPart(delta)
	{}

	TRational::~TRational(){}

	
	/**************************************
			OVERLOAD OPERATORS
	**************************************/

	/**
	 * 
	 * @param _value
	 * @return
	*/
	TRational& TRational::operator=(const TRational& _value){
		rationalPart = _value.getRationalPart();
        deltaPart = _value.getDeltaPart();
        return *this;
	}

	/**
     * 
     * @param _value
     * @return
    */
    TRational TRational::operator +( const TRational& _value) const{
		Rational first = rationalPart + _value.getRationalPart();
        Rational second = deltaPart + _value.getDeltaPart();
        return TRational(first, second);
    }

    /**
     * 
     * @param _value
    */
 	void TRational::operator +=( const TRational& _value ){
 		this->rationalPart += _value.getRationalPart();
        this->deltaPart += _value.getDeltaPart();
 	}	


} // smtrat


