"use strict";

(function(){

const $JSRTS = {
    throw: function (x) {
        throw x;
    },
    Lazy: function (e) {
        this.js_idris_lazy_calc = e;
        this.js_idris_lazy_val = void 0;
    },
    force: function (x) {
        if (x === undefined || x.js_idris_lazy_calc === undefined) {
            return x
        } else {
            if (x.js_idris_lazy_val === undefined) {
                x.js_idris_lazy_val = x.js_idris_lazy_calc()
            }
            return x.js_idris_lazy_val
        }
    },
    prim_strSubstr: function (offset, len, str) {
        return str.substr(Math.max(0, offset), Math.max(0, len))
    }
};
$JSRTS.prim_systemInfo = function (index) {
    switch (index) {
        case 0:
            return "javascript";
        case 1:
            return navigator.platform;
    }
    return "";
};
$JSRTS.prim_writeStr = function (x) { return console.log(x) }
$JSRTS.prim_readStr = function () { return prompt('Prelude.getLine') };



function $partial_0_1$Main___123_main_95_0_125_(){
    return (function(x1){
        return Main___123_main_95_0_125_(x1);
    });
}

const $HC_0_0$TheWorld = ({type: 0});
// Main.amain

function Main__amain($_0_w){
    return (amain());
}

// Main.setIncrementer

function Main__setIncrementer($_0_arg, $_1_w){
    return (setIncrementer(($_0_arg)));
}

// Main.{main_0}

function Main___123_main_95_0_125_($_0_lift){
    return (1 + $_0_lift);
}

// {runMain_0}

function $_0_runMain(){
    const $_6_in = Main__setIncrementer($partial_0_1$Main___123_main_95_0_125_(), $HC_0_0$TheWorld);
    return $JSRTS.force(Main__amain($HC_0_0$TheWorld));
}


$_0_runMain();
}.call(this))