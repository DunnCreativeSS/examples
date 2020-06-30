# This code is for sample purposes only, comes as is and with no warranty or guarantee of performance

from collections    import OrderedDict
from datetime       import datetime
from os.path        import getmtime
from time           import sleep
import linecache
from utils          import ( get_logger, lag, print_dict, print_dict_of_dicts, sort_by_key,
                             ticksize_ceil, ticksize_floor, ticksize_round )
def PrintException():
    exc_type, exc_obj, tb = sys.exc_info()
    f = tb.tb_frame
    lineno = tb.tb_lineno
    filename = f.f_code.co_filename
    linecache.checkcache(filename)
    line = linecache.getline(filename, lineno, f.f_globals)
    string = 'EXCEPTION IN ({}, LINE {} "{}"): {}'.format(filename, lineno, line.strip(), exc_obj)
    print(string)
    
import copy as cp
import argparse, logging, math, os, pathlib, sys, time, traceback

try:
    from deribit_api    import RestClient
except ImportError:
    #print("Please install the deribit_api pacakge", file=sys.stderr)
    #print("    pip3 install deribit_api", file=sys.stderr)
    exit(1)

# Add command line switches
parser  = argparse.ArgumentParser( description = 'Bot' )

# Use production platform/account
parser.add_argument( '-p',
                     dest   = 'use_prod',
                     action = 'store_true' )

# Do not display regular status updates to terminal
parser.add_argument( '--no-output',
                     dest   = 'output',
                     action = 'store_false' )

# Monitor account only, do not send trades
parser.add_argument( '-m',
                     dest   = 'monitor',
                     action = 'store_true' )

# Do not restart bot on errors
parser.add_argument( '--no-restart',
                     dest   = 'restart',
                     action = 'store_false' )

args    = parser.parse_args()

KEY     = 'JemK0AgA'
SECRET  = 'BhCLfGEtD9L-h7fsZJ2VI-bW2L7W0C65eiktjkRz7xs'
URL     = 'https://test.deribit.com' #www.


        
BP                  = 1e-4      # one basis point
BTC_SYMBOL          = 'btc'
CONTRACT_SIZE       = 10        # USD
COV_RETURN_CAP      = 100       # cap on variance for vol estimate
DECAY_POS_LIM       = 0.1       # position lim decay factor toward expiry
EWMA_WGT_COV        = 4         # parameter in % points for EWMA volatility estimate
EWMA_WGT_LOOPTIME   = 0.1       # parameter for EWMA looptime estimate
FORECAST_RETURN_CAP = 20        # cap on returns for vol estimate
LOG_LEVEL           = logging.INFO
MIN_ORDER_SIZE      = 10
MAX_LAYERS          =  3        # max orders to layer the ob with on each side
MKT_IMPACT          =  0.5      # base 1-sided spread between bid/offer
NLAGS               =  2        # number of lags in time series
PCT                 = 100 * BP  # one percentage point
PCT_LIM_LONG        = 100       # % position limit long
PCT_LIM_SHORT       = 200       # % position limit short
PCT_QTY_BASE        = 100       # pct order qty in bps as pct of acct on each order
MIN_LOOP_TIME       =   0.2       # Minimum time between loops
RISK_CHARGE_VOL     =   0.25    # vol risk charge in bps per 100 vol
SECONDS_IN_DAY      = 3600 * 24
SECONDS_IN_YEAR     = 365 * SECONDS_IN_DAY
WAVELEN_MTIME_CHK   = 15        # time in seconds between check for file change
WAVELEN_OUT         = 15        # time in seconds between output to terminal
WAVELEN_TS          = 15        # time in seconds between time series update
VOL_PRIOR           = 100       # vol estimation starting level in percentage pts
LEVERAGE_MAX = 50

RATE_LIMIT = 0.2 #secs
EWMA_WGT_COV        *= PCT
MKT_IMPACT          *= BP
PCT_LIM_LONG        *= PCT
PCT_LIM_SHORT       *= PCT
PCT_QTY_BASE        *= BP
VOL_PRIOR           *= PCT


class MarketMaker( object ):
    
    def __init__( self, monitor = True, output = True ):
        self.longperp = None
        self.equity_usd         = None
        self.LEV_LIM = {}
        self.place_asks = {}
        self.place_bids = {}
        self.skew_size = {}
        self.LEV = 0
        self.IM = 0
        self.MAX_SKEW = 0
        self.equity_btc         = None
        self.equity_usd_init    = None
        self.equity_btc_init    = None
        self.con_size           = float( CONTRACT_SIZE )
        self.client             = None
        self.deltas             = OrderedDict()
        self.futures            = OrderedDict()
        self.futures_prv        = OrderedDict()
        self.logger             = None
        self.mean_looptime      = 1
        self.monitor            = monitor
        self.output             = output or monitor
        self.positions          = OrderedDict()
        self.spread_data        = None
        self.this_mtime         = None
        self.ts                 = None
        self.vols               = OrderedDict()
    
    
    def create_client( self ):
        self.client = RestClient( KEY, SECRET, URL )
    
    
    def get_bbo( self, contract ): # Get best b/o excluding own orders
        
        # Get orderbook
        ob      = self.client.getorderbook( contract )
        bids    = ob[ 'bids' ]
        asks    = ob[ 'asks' ]
        
        ords        = self.client.getopenorders( contract )
        bid_ords    = [ o for o in ords if o[ 'direction' ] == 'buy'  ]
        ask_ords    = [ o for o in ords if o[ 'direction' ] == 'sell' ]
        best_bid    = None
        best_ask    = None

        err = 10 ** -( self.get_precision( contract ) + 1 )
        
        for b in bids:
            match_qty   = sum( [ 
                o[ 'quantity' ] for o in bid_ords 
                if math.fabs( b[ 'price' ] - o[ 'price' ] ) < err
            ] )
            if match_qty < b[ 'quantity' ]:
                best_bid = b[ 'price' ]
                break
        
        for a in asks:
            match_qty   = sum( [ 
                o[ 'quantity' ] for o in ask_ords 
                if math.fabs( a[ 'price' ] - o[ 'price' ] ) < err
            ] )
            if match_qty < a[ 'quantity' ]:
                best_ask = a[ 'price' ]
                break
        
        return { 'bid': best_bid, 'ask': best_ask }
    
        
    def get_futures( self ): # Get all current futures instruments
        
        self.futures_prv    = cp.deepcopy( self.futures )
        insts               = self.client.getinstruments()
        self.futures        = sort_by_key( { 
            i[ 'instrumentName' ]: i for i in insts  if i[ 'kind' ] == 'future'  and 'BTC' in i['instrumentName'] 
        } )
        
        for k, v in self.futures.items():
            self.futures[ k ][ 'expi_dt' ] = datetime.strptime( 
                                                v[ 'expiration' ][ : -4 ], 
                                                '%Y-%m-%d %H:%M:%S' )
                        
        
    def get_pct_delta( self ):         
        self.update_status()
        return sum( self.deltas.values()) / self.equity_btc

    
    def get_spot( self ):
        return self.client.index()[ 'btc' ]

    
    def get_precision( self, contract ):
        return self.futures[ contract ][ 'pricePrecision' ]

    
    def get_ticksize( self, contract ):
        return self.futures[ contract ][ 'tickSize' ]
    
    
    def output_status( self ):
        
        if not self.output:
            return None
        
        self.update_status()
        
        now     = datetime.utcnow()
        days    = ( now - self.start_time ).total_seconds() / SECONDS_IN_DAY
        #print( '********************************************************************' )
        #print( 'Start Time:        %s' % self.start_time.strftime( '%Y-%m-%d %H:%M:%S' ))
        #print( 'Current Time:      %s' % now.strftime( '%Y-%m-%d %H:%M:%S' ))
        #print( 'Days:              %s' % round( days, 1 ))
        #print( 'Hours:             %s' % round( days * 24, 1 ))
        #print( 'Spot Price:        %s' % self.get_spot())
        
        
        pnl_usd = self.equity_usd - self.equity_usd_init
        pnl_btc = self.equity_btc - self.equity_btc_init
        
        #print( 'Equity ($):        %7.2f'   % self.equity_usd)
        #print( 'P&L ($)            %7.2f'   % pnl_usd)
        #print( 'Equity (BTC):      %7.4f'   % self.equity_btc)
        #print( 'P&L (BTC)          %7.4f'   % pnl_btc)
        #print( '%% Delta:           %s%%'% round( self.get_pct_delta() / PCT, 1 ))
        #print( 'Total Delta (BTC): %s'   % round( sum( self.deltas.values()), 2 ))        
        print_dict_of_dicts( {
            k: {
                'BTC': self.deltas[ k ]
            } for k in self.deltas.keys()
            }, 
            roundto = 2, title = 'Deltas' )
        
        print_dict_of_dicts( {
            k: {
                'Contracts': self.positions[ k ][ 'size' ]
            } for k in self.positions.keys()
            }, 
            title = 'Positions' )
        
        if not self.monitor:
            print_dict_of_dicts( {
                k: {
                    '%': self.vols[ k ]
                } for k in self.vols.keys()
                }, 
                multiple = 100, title = 'Vols' )
            #print( '\nMean Loop Time: %s' % round( self.mean_looptime, 2 ))
            
        #print( '' )

        
    def place_orders( self ):

        if self.monitor:
            return None
        
        con_sz  = self.con_size        
        print(['BTC-PERPETUAL', 'BTC-25DEC20', 'BTC-25SEP20', 'BTC-26MAR21'])
        for fut in ['BTC-PERPETUAL', 'BTC-25DEC20', 'BTC-25SEP20', 'BTC-26MAR21']:
            print(fut)
            account         = self.client.account()
            spot            = self.get_spot()
            bal_btc         = account[ 'equity' ]
            pos             = self.positions[ fut ][ 'sizeBtc' ]
            
            expi            = self.futures[ fut ][ 'expi_dt' ]
            tte             = max( 0, ( expi - datetime.utcnow()).total_seconds() / SECONDS_IN_DAY )
            pos_decay       = 1.0 - math.exp( -DECAY_POS_LIM * tte )
            
            
            min_order_size_btc = MIN_ORDER_SIZE / spot * CONTRACT_SIZE
            qtybtc  = max( PCT_QTY_BASE  * bal_btc, min_order_size_btc)
            nbids   = MAX_LAYERS
            nasks   = MAX_LAYERS
            
            #place_bids = nbids > 0
            #place_asks = nasks > 0
            self.MAX_SKEW = MIN_ORDER_SIZE * MAX_LAYERS * 10
            #print(fut)
            
            
            spot    = self.get_spot()
            ##print(res) 
            t = 0
            for pos in self.positions:
                t = t + math.fabs(self.positions[pos]['size'])
            self.equity_usd = self.equity_btc * spot
            self.LEV = t / self.equity_usd
            self.IM = self.LEV / 2
            
            ##print(' ')
            ##print(fut)
            ##print(' ')
            for k in self.positions:
                self.skew_size[k[0:3]] = 0
            ####print('skew_size: ' + str(self.skew_size))
            ####print(self.positions)
            for k in self.positions:
                self.skew_size[k[0:3]] = self.skew_size[k[0:3]] + self.positions[k]['size']
                ####print('skew_size: ' + str(self.skew_size))
            #print(self.skew_size)
            psize = self.positions[fut]['size']
            self.place_bids[fut] = True
            self.place_asks[fut] = True
            ###print(self.PCT_LIM_LONG)
            a = {}
            

            for pos in self.positions:
                a[pos] = 0
            
            for pos in self.positions:
                a[pos] = a[pos] + math.fabs(self.positions[pos]['size'])
            
            ##print((((a[pos[0:3]] / self.equity_usd) / self.LEV_LIM[pos[0:3]] * 1000 ) / 10 ))
            ##print((((a[pos[0:3]] / self.equity_usd) / self.LEV_LIM[pos[0:3]] * 1000 ) / 10 ))
            ##print((((a[pos[0:3]] / self.equity_usd) / self.LEV_LIM[pos[0:3]] * 1000 ) / 10 ))
            #print(self.LEV_LIM)
            #print(a)
            if self.LEV_LIM[fut] == 0:
                ##print('lev lim 0!')
                if self.positions[fut]['size'] < 0:
                    self.place_asks[fut] = False
                if self.positions[fut]['size'] > 0:
                    self.place_bids[fut] = False
            elif (((a[fut] / self.equity_usd) / self.LEV_LIM[fut] * 1000 ) / 10 ) > 100:
                if self.positions[fut]['size'] < 0:
                    self.place_asks[fut] = False
                if self.positions[pos]['size'] > 0:
                    self.place_bids[pos] = False
                #print((((a[fut] / self.equity_usd) / self.LEV_LIM[fut] * 1000 ) / 10 ))

            if self.place_asks[fut] == False and self.place_bids[fut] == False:
                try:
                    
                    prc = self.get_bbo(fut)['bid']
                    
                    qty = self.equity_usd / 48  / 10 / 2
                    qty = float(min( qty, MIN_ORDER_SIZE))
                    # 
                    ###print('qty: ' + str(qty)) 
                    ###print(max_bad_arb)
                    
                    qty = round(qty)  
                    for k in self.positions:
                        self.skew_size[k[0:3]] = 0

                    for k in self.positions:
                        self.skew_size[k[0:3]] = self.skew_size[k[0:3]] + self.positions[k]['size'] 
                    token = fut[0:3] 
                    if 'ETH' in fut or 'XRP' in fut:
                        qty = qty / self.get_bbo(fut[0:3] + 'USD')['bid']
                        if 'USD' in fut:
                            qty = qty / self.get_multiplier(fut)
                    if qty <= 1:
                        qty = 1


                    if self.positions[fut]['size'] >= 0:
                        ##print(' ')
                        ##print(' ')
                        ##print(qty)
                        ##print(self.skew_size[token])
                        ##print(self.MAX_SKEW)
                        if qty + self.skew_size[token] * -1 <= self.MAX_SKEW:
                            mexAsks = []
                            for i in range(0, round(MAX_LAYERS)):
                                r = random.randint(0, 100)
                                #print(r)
                                if qty + self.skew_size[fut[0:3]] * -1 <  self.MAX_SKEW:
                                    
                                    if i >= len_ask_ords:
                                        self.client.sell( fut, qty, asks[i], 'true' )
                            

                    if self.positions[fut]['size'] <= 0:
                        if qty + self.skew_size[token] < self.MAX_SKEW:

                            mexBids = []
                            for i in range(0, round(MAX_LAYERS)):

                                r = random.randint(0, 100)
                                #print(r)
                                if qty + self.skew_size[fut[0:3]] <  self.MAX_SKEW:
                                    
                                    if i >= len_bid_ords:
                                        self.client.buy( fut, qty, bids[i], 'true' )
                           

                    
                except:
                    PrintException()
                
               
                
            tsz = self.get_ticksize( fut )            
            # Perform pricing
            

            bbo     = self.get_bbo( fut )
            bid_mkt = bbo[ 'bid' ]
            ask_mkt = bbo[ 'ask' ]
            
            if bid_mkt is None and ask_mkt is None:
                bid_mkt = ask_mkt = spot
            elif bid_mkt is None:
                bid_mkt = min( spot, ask_mkt )
            elif ask_mkt is None:
                ask_mkt = max( spot, bid_mkt )
            mid_mkt = 0.5 * ( bid_mkt + ask_mkt )
            
            ords        = self.client.getopenorders( fut )
            cancel_oids = []
            bid_ords    = ask_ords = []
            riskfac = 1
            asks = []
            bids = []
            if self.place_bids[fut]:
                
                bid_ords        = [ o for o in ords if o[ 'direction' ] == 'buy'  ]
                len_bid_ords    = min( len( bid_ords ), nbids )
                bid0            = mid_mkt * math.exp( -MKT_IMPACT )
                
                bids    = [ bid0 * riskfac ** -i for i in range( 1, nbids + 1 ) ]

                bids[ 0 ]   = ticksize_floor( bids[ 0 ], tsz )
                
            if self.place_asks[fut]:
                
                ask_ords        = [ o for o in ords if o[ 'direction' ] == 'sell' ]    
                len_ask_ords    = min( len( ask_ords ), nasks )
                ask0            = mid_mkt * math.exp(  MKT_IMPACT )
                
                asks    = [ ask0 * riskfac ** i for i in range( 1, nasks + 1 ) ]
                
                asks[ 0 ]   = ticksize_ceil( asks[ 0 ], tsz  )
            nbids = len(bids)
            nasks = len(asks)
            # BIDS
            for i in range( 0, MAX_LAYERS ):
                if i < nbids:
                    ###print(i)
                    if i > 0:
                        prc = ticksize_floor( min( bids[ i ], bids[ i - 1 ] - tsz ), tsz )
                    else:
                        prc = bids[ 0 ]

                    #qty = ( prc * qtybtc / con_sz )  
                    qty = self.equity_usd / 48  / 10 / 2
                    qty = float(min( qty, MIN_ORDER_SIZE))
                    max_bad_arb = int(self.MAX_SKEW )
                    # 
                    ###print('qty: ' + str(qty)) 
                    ###print(max_bad_arb)
                    qty = qty 
                    qty = round(qty) * (i+1)    
                    if qty <= 1:
                        qty = 1   
                    ###print('qty: ' + str(qty))    
                    if self.MAX_SKEW < qty * 10 :
                        self.MAX_SKEW = qty * 10  
                    if self.place_asks[fut] == False:
                        self.MAX_SKEW = self.MAX_SKEW * 3
                        qty = qty * 10
                        ob    = self.client.getorderbook( fut )
                        bids1    = ob[ 'bids' ]
                        asks1   = ob[ 'asks' ]
                        prc = ticksize_floor(( bids1[0]['price']), tsz )
                    if qty + self.skew_size[fut[0:3]] >  self.MAX_SKEW:
                        print(fut+ ' bid self.MAX_SKEW return ...')
                        for xyz in bid_ords:
                            cancel_oids.append( xyz['orderId'] )

                        #self.execute_cancels(fut, nbids, nasks, bid_ords, ask_ords, qtybtc, con_sz, tsz, cancel_oids, len_bid_ords, len_ask_ords)
                            
                        continue
                    ##print(len_bid_ords)
                        ###print('i less')
                    try:
                        if i < len_bid_ords:    
                            sleep(RATE_LIMIT)
                            ###print('i less')
                            try:
                                oid = bid_ords[ i ][ 'orderId' ]
                                self.restartflag = False
                                self.client.edit( oid, qty, prc )
                            except (SystemExit, KeyboardInterrupt):
                                raise
                            except Exception as e:
                                PrintException()
                        elif len_bid_ords <= MAX_LAYERS:
                            if 'PERPETUAL' not in fut:
                                if self.longperp == False:
                                    if self.arbmult[fut]['arb'] > 0 and (self.positions[fut]['size'] - qty <= max_bad_arb ):
                                        if 'ETH' in fut or 'XRP' in fut:
                                            qty = qty / self.get_bbo(fut[0:3] + 'USD')['bid']
                                            if 'USD' in fut:
                                                qty = qty / self.get_multiplier(fut)
                                            if qty <= 1:
                                                qty = 1

                                        self.restartflag = False
                                        self.client.buy( fut, qty, prc, 'true' )
                                        

                                    if self.arbmult[fut]['arb'] < 0 :
                                        if 'ETH' in fut or 'XRP' in fut:
                                            qty = qty / self.get_bbo(fut[0:3] + 'USD')['bid']
                                            if 'USD' in fut:
                                                qty = qty / self.get_multiplier(fut)
                                        qty = int(qty * 3)
                                        ###print('buy qty * 1.1, 1' + fut)
                                        if qty <= 1:
                                            qty = 1

                                        self.restartflag = False
                                        self.client.buy( fut, qty, prc, 'true' )
                            else:
                                print(self.longperp)
                                if self.longperp == True:
                                    qty = qty * 2
                                    print(qty)
                                    print(self.arbmult[fut]['arb'])
                                    print(self.positions[fut]['size'])
                                    print(max_bad_arb)
                                    if self.arbmult[fut]['arb'] < 0 and (self.positions[fut]['size'] - qty <= max_bad_arb ):
                                        if 'ETH' in fut or 'XRP' in fut:
                                            qty = qty / self.get_bbo(fut[0:3] + 'USD')['bid']
                                            if 'USD' in fut:
                                                qty = qty / self.get_multiplier(fut)
                                            if qty <= 1:
                                                qty = 1

                                        self.restartflag = False
                                        self.client.buy( fut, qty, prc, 'true' )
                                        

                                    if self.arbmult[fut]['arb'] > 0:
                                        if 'ETH' in fut or 'XRP' in fut:
                                            qty = qty / self.get_bbo(fut[0:3] + 'USD')['bid']
                                            if 'USD' in fut:
                                                qty = qty / self.get_multiplier(fut)
                                        qty = int(qty * 3)
                                        ###print('buy qty * 1.1, 2' + fut)
                                        if qty <= 1:
                                            qty = 1

                                        self.restartflag = False
                                        self.client.buy( fut, qty, prc, 'true' )
                        elif len_bid_ords <= MAX_LAYERS:
                            sleep(RATE_LIMIT)
                            if 'PERPETUAL' not in fut:
                                if self.longperp == False:
                                    if self.arbmult[fut]['arb'] > 0 and (self.positions[fut]['size'] - qty <= max_bad_arb ):
                                        if 'ETH' in fut or 'XRP' in fut:
                                            qty = qty / self.get_bbo(fut[0:3] + 'USD')['bid']
                                            if 'USD' in fut:
                                                qty = qty / self.get_multiplier(fut)
                                            if qty <= 1:
                                                qty = 1

                                        self.restartflag = False
                                        self.client.buy( fut, qty, prc, 'true' )
                                        

                                    if self.arbmult[fut]['arb'] < 0 :
                                        if 'ETH' in fut or 'XRP' in fut:
                                            qty = qty / self.get_bbo(fut[0:3] + 'USD')['bid']
                                            if 'USD' in fut:
                                                qty = qty / self.get_multiplier(fut)
                                        qty = int(qty * 3)
                                        ###print('buy qty * 1.1, 1' + fut)
                                        if qty <= 1:
                                            qty = 1

                                        self.restartflag = False
                                        self.client.buy( fut, qty, prc, 'true' )
                            else:
                                if self.longperp == True:
                                    
                                    qty = qty * 2
                                    if self.arbmult[fut]['arb'] < 0 and (self.positions[fut]['size'] - qty <= max_bad_arb ):
                                        if 'ETH' in fut or 'XRP' in fut:
                                            qty = qty / self.get_bbo(fut[0:3] + 'USD')['bid']
                                            if 'USD' in fut:
                                                qty = qty / self.get_multiplier(fut)
                                            if qty <= 1:
                                                qty = 1

                                        self.restartflag = False
                                        self.client.buy( fut, qty, prc, 'true' )
                                        

                                    if self.arbmult[fut]['arb'] > 0:
                                        if 'ETH' in fut or 'XRP' in fut:
                                            qty = qty / self.get_bbo(fut[0:3] + 'USD')['bid']
                                            if 'USD' in fut:
                                                qty = qty / self.get_multiplier(fut)
                                        qty = int(qty * 3)
                                        ###print('buy qty * 1.1, 2' + fut)
                                        if qty <= 1:
                                            qty = 1

                                        self.restartflag = False
                                        self.client.buy( fut, qty, prc, 'true' )               

                                
                            
                    except (SystemExit, KeyboardInterrupt):
                        raise
                    except Exception as e:
                        PrintException()
                        self.logger.warn( 'Bid order failed: %s bid for %s'
                                        % ( prc, qty ))
             
                # OFFERS
                # ASKS
                ###print('# OFFERS')

                if i < nasks:

                    if i > 0:
                        prc = ticksize_ceil( max( asks[ i ], asks[ i - 1 ] + tsz ), tsz )
                    else:
                        prc = asks[ 0 ]
                        
                    qty = self.equity_usd / 48  / 10 / 2

                    qty = float(min( qty, MIN_ORDER_SIZE))
                    
                    #10
                    
                    max_bad_arb = int(self.MAX_SKEW )
                    ###print('qty: ' + str(qty)) 
                    ###print(max_bad_arb)
                    

                    qty = qty 
                    qty = round(qty)   * (i+1)  

                    if qty <= 1:
                        qty = 1   
                    if self.MAX_SKEW < qty * 10 :
                        self.MAX_SKEW = qty * 10 
                    if self.place_bids[fut] == False:
                        self.MAX_SKEW = self.MAX_SKEW * 3
                        qty = qty * 10
                        ob    = self.client.getorderbook( fut )
                        bids1    = ob[ 'bids' ]
                        asks1   = ob[ 'asks' ]
                        prc = ticksize_ceil(( asks1[0]['price']), tsz )
                    ###print('qty: ' + str(qty))       
                    ####print('skew_size: ' + str(self.skew_size))
                    ####print('max_soew: ' + str(self.MAX_SKEW))
                    if qty + self.skew_size[fut[0:3]] * -1 >  self.MAX_SKEW:
                        print(fut + ' offer self.MAX_SKEW return ...')
                        for xyz in ask_ords:
                            cancel_oids.append( xyz['orderId'] )

                            
                        #self.execute_cancels(fut, nbids, nasks, bid_ords, ask_ords, qtybtc, con_sz, tsz, cancel_oids, len_bid_ords, len_ask_ords)
                        continue
                    ##print(len_ask_ords)
                    try:
                        if i < len_ask_ords:    
                            sleep(RATE_LIMIT)
                            ###print('i less')
                            try:
                                oid = ask_ords[ i ][ 'orderId' ]
                                
                                self.restartflag = False
                                self.client.edit( oid, qty, prc )
                            except (SystemExit, KeyboardInterrupt):
                                raise
                            except Exception as e:
                                PrintException()
                        elif len_ask_ords <= MAX_LAYERS:
                            if 'PERPETUAL' not in fut:
                                if self.longperp == True:
                                    if self.arbmult[fut]['arb'] >= 0:
                                        if 'ETH' in fut or 'XRP' in fut:
                                            qty = qty / self.get_bbo(fut[0:3] + 'USD')['bid']
                                            
                                            if 'USD' in fut:
                                                qty = qty / self.get_multiplier(fut)
                                        qty = int(qty * 3)
                                        ###print('sell qty * 1.1, 1' + fut)
                                        if qty <= 1:
                                            qty = 1

                                        self.restartflag = False
                                        self.client.sell( fut, qty, prc, 'true' )#self.client.sell( fut, qty, prc, 'true' )

                                        
                                    
                                    if self.arbmult[fut]['arb'] <= 0 and self.positions[fut]['size'] + qty * -1 >=-1 * max_bad_arb  :
                                        if 'ETH' in fut or 'XRP' in fut:
                                            qty = qty / self.get_bbo(fut[0:3] + 'USD')['bid']
                                            if 'USD' in fut:
                                                qty = qty / self.get_multiplier(fut)
                                            if qty <= 1:
                                                qty = 1

                                        self.restartflag = False
                                        self.client.sell( fut, qty, prc, 'true' )#self.client.sell(  fut, qty, prc, 'true' )
                            else:
                                if self.longperp == False:
                                    #print(self.arbmult)
                                    qty = qty * 2
                                    if self.arbmult[fut]['arb'] <= 0:
                                        if 'ETH' in fut or 'XRP' in fut:
                                            qty = qty / self.get_bbo(fut[0:3] + 'USD')['bid']
                                            
                                            if 'USD' in fut:
                                                qty = qty / self.get_multiplier(fut)
                                        qty = int(qty * 3)
                                        ###print('sell qty * 1.1, 2' + fut)
                                        if qty <= 1:
                                            qty = 1

                                        self.restartflag = False
                                        self.client.sell( fut, qty, prc, 'true' )#self.client.sell( fut, qty, prc, 'true' )

                                        
                                    
                                    if self.arbmult[fut]['arb'] >= 0 and self.positions[fut]['size'] + qty * -1 >=-1 * max_bad_arb  :
                                        if 'ETH' in fut or 'XRP' in fut:
                                            qty = qty / self.get_bbo(fut[0:3] + 'USD')['bid']
                                            if 'USD' in fut:
                                                qty = qty / self.get_multiplier(fut)
                                            if qty <= 1:
                                                qty = 1

                                        self.restartflag = False
                                        self.client.sell( fut, qty, prc, 'true' )#self.client.sell(  fut, qty, prc, 'true' )
                        elif len_ask_ords <= MAX_LAYERS:
                            sleep(RATE_LIMIT)
                            if 'PERPETUAL' not in fut:
                                if self.longperp == True:
                                    if self.arbmult[fut]['arb'] >= 0:
                                        if 'ETH' in fut or 'XRP' in fut:
                                            qty = qty / self.get_bbo(fut[0:3] + 'USD')['bid']
                                            
                                            if 'USD' in fut:
                                                qty = qty / self.get_multiplier(fut)
                                        qty = int(qty * 3)
                                        ###print('sell qty * 1.1, 1' + fut)
                                        if qty <= 1:
                                            qty = 1

                                        self.restartflag = False
                                        self.client.sell( fut, qty, prc, 'true' )#self.client.sell( fut, qty, prc, 'true' )

                                        
                                    
                                    if self.arbmult[fut]['arb'] <= 0 and self.positions[fut]['size'] + qty * -1 >=-1 * max_bad_arb  :
                                        if 'ETH' in fut or 'XRP' in fut:
                                            qty = qty / self.get_bbo(fut[0:3] + 'USD')['bid']
                                            if 'USD' in fut:
                                                qty = qty / self.get_multiplier(fut)
                                            if qty <= 1:
                                                qty = 1

                                        self.restartflag = False
                                        self.client.sell( fut, qty, prc, 'true' )#self.client.sell(  fut, qty, prc, 'true' )
                            else:
                                if self.longperp == False:
                                    qty = qty * 2
                                    if self.arbmult[fut]['arb'] <= 0:
                                        if 'ETH' in fut or 'XRP' in fut:
                                            qty = qty / self.get_bbo(fut[0:3] + 'USD')['bid']
                                            
                                            if 'USD' in fut:
                                                qty = qty / self.get_multiplier(fut)
                                        qty = int(qty * 3)
                                        ###print('sell qty * 1.1, 2' + fut)
                                        if qty <= 1:
                                            qty = 1

                                        self.restartflag = False
                                        self.client.sell( fut, qty, prc, 'true' )#self.client.sell( fut, qty, prc, 'true' )

                                        
                                    
                                    if self.arbmult[fut]['arb'] >= 0 and self.positions[fut]['size'] + qty * -1 >=-1 * max_bad_arb  :
                                        if 'ETH' in fut or 'XRP' in fut:
                                            qty = qty / self.get_bbo(fut[0:3] + 'USD')['bid']
                                            if 'USD' in fut:
                                                qty = qty / self.get_multiplier(fut)
                                            if qty <= 1:
                                                qty = 1

                                        self.restartflag = False
                                        self.client.sell( fut, qty, prc, 'true' )#self.client.sell(  fut, qty, prc, 'true' )
                    
                                    

                                
                    except (SystemExit, KeyboardInterrupt):
                        raise
                    except Exception as e:
                        PrintException()
                        self.logger.warn( 'Offer order failed: %s at %s'
                                        % ( qty, prc ))

            if nbids < len( bid_ords ):
                cancel_oids += [ o[ 'orderId' ] for o in bid_ords[ nbids : ]]
            if nasks < len( ask_ords ):
                cancel_oids += [ o[ 'orderId' ] for o in ask_ords[ nasks : ]]
            for oid in cancel_oids:
                try:
                    self.client.cancel( oid )
                except:
                    self.logger.warn( 'Order cancellations failed: %s' % oid )
                                        
    
    def restart( self ):        
        try:
            strMsg = 'RESTARTING'
            #print( strMsg )
            self.client.cancelall()
            strMsg += ' '
            for i in range( 0, 5 ):
                strMsg += '.'
                #print( strMsg )
                sleep( 1 )
        except:
            pass
        finally:
            os.execv( sys.executable, [ sys.executable ] + sys.argv )        
            

    def run( self ):
        
        self.run_first()
        self.output_status()

        t_ts = t_out = t_loop = t_mtime = datetime.utcnow()

        while True:
            bbos = []
            arbs = {}
            #self.client.buy(  'BTC-PERPETUAL', size, mid * 1.02)
            expdays = {}
            for k in self.futures.keys():
                bbo  = self.get_bbo( k[0:3] + '-PERPETUAL' )
                bid_mkt = bbo[ 'bid' ]
                ask_mkt = bbo[ 'ask' ]
                mid = 0.5 * ( bbo[ 'bid' ] + bbo[ 'ask' ] )

                m = self.get_bbo(k)
                
                bid = m['bid']
                ask=m['ask']
                mid1 = 0.5 * (bid + ask)
                if k == 'ETHM20' or k == 'XRPM20':
                    mid1 = mid1 * self.get_spot()
                arb = mid1 / mid
                arbs[k] = float(arb)
                #if 'PERPETUAL' not in k:
                    ###print('perp is ' + str(mid) + ' ' + k + ' is ' + str(mid1) + ' and arb is ' + str(arb)  + ' positive is sell negative is bbuy')
                
                expsecs = (self.futures[k]['expi_dt'] - datetime.now()).total_seconds()
                
                expday = expsecs / 60 / 24
                expdays[k]=float(expday)
                bbos.append({k: mid1 - self.get_spot()})
            fundvsprem = {}
            newarbs = {}
            self.arbmult = {}
            for k in arbs:
                if 'PERPETUAL' not in k:
                    doin = ((-1*(1-arbs[k]) / expdays[k])* 100) 
                    ###print(k[0:3])
                    #print(k + '! Premium arb is ' + str(math.fabs(doin)) + ' %!')
                    fundvsprem[k] = 'premium'
                    newarbs[k] = doin
                    self.arbmult[k] = {}
            arbs = newarbs

                
            for token in arbs:
                
                if arbs[token] < 0:
                    self.arbmult[token] = ({'coin': token, 'long': 'futs', 'short': 'perp', 'arb': (arbs[token])})
                else:
                    self.arbmult[token] = ({'coin': token, 'long': 'perp', 'short': 'futs', 'arb': (arbs[token])})
            #funding: {'ETH': {'coin': 'ETH', 'long': 'futs', 'short': 'perp', 'arb': -0.00030000000000000003}, 'XBT': {'coin': 'XBT', 'long': 'perp', 'short': 'futs', 'arb': 0.000153}, 'XRP': {'coin': 'XRP', 'long': 'futs', 'short': 'perp', 'arb': -0.0007440000000000001}}
            #premium: {'ETH': {'coin': 'ETH', 'long': 'futs', 'short': 'perp', 'arb': -0.00013291636050582245}, 'XBT': {'coin': 'XBT', 'long': 'perp', 'short': 'futs', 'arb': 3.722894995661838e-05}, 'XRP': {'coin': 'XRP', 'long': 'futs', 'short': 'perp', 'arb': -6.462857850516617e-05}}
            perplongs = 0
            perpshorts = 0
            for arb in self.arbmult:
                if self.arbmult[arb]['long'] == 'perp':
                    perplongs = perplongs + 1
                else:
                    perpshorts = perpshorts + 1
            if perplongs >= perpshorts:
                self.longperp = True
                self.arbmult['BTC-PERPETUAL'] = ({'coin': 'BTC-PERPETUAL', 'long': 'perp', 'short': 'futs', 'arb': 0.5})
            else:
                self.longperp = False
                self.arbmult['BTC-PERPETUAL'] = ({'coin': 'BTC-PERPETUAL', 'long': 'futs', 'short': 'perp', 'arb': -0.5})
            #print('self.longpperp? ' + str(self.longperp))
            #print(self.arbmult)
            t = 0
            c = 0
            for arb in self.arbmult:
                t = t + math.fabs(self.arbmult[arb]['arb'])

                c = c + 1
            #print('t: ' + str(t))
            
            for arb in self.arbmult:
                self.arbmult[arb]['perc'] = math.fabs(round((self.arbmult[arb]['arb']) / t * 1000) / 1000) #* 1.41425
                
            #print(self.arbmult)
            ##print(self.arbmult)
            for coin in arbs:
                self.LEV_LIM[coin] = LEVERAGE_MAX / 2
            for coin in arbs:
                self.LEV_LIM[coin] = self.LEV_LIM[coin] * self.arbmult[coin]['perc'] 
                
            self.LEV_LIM['BTC-PERPETUAL'] = LEVERAGE_MAX / 2
            #print(self.LEV_LIM)
            skewingpos = 0
            skewingneg = 0
            positionSize = 0
            for p in self.positions:
                positionSize = positionSize + self.positions[p]['size']
                if self.positions[p]['size'] > 0:
                    skewingpos = skewingpos + 1
                elif self.positions[p]['size'] < 0:
                    skewingneg = skewingneg + 1
            self.get_futures()
            
            # Restart if a new contract is listed
            if len( self.futures ) != len( self.futures_prv ):
                self.restart()
            
            self.update_positions()
            
            t_now   = datetime.utcnow()
            
            # Update time series and vols
            if ( t_now - t_ts ).total_seconds() >= WAVELEN_TS:
                t_ts = t_now
                self.update_timeseries()
                self.update_vols()
    
            self.place_orders()
            
            # Display status to terminal
            if self.output:    
                t_now   = datetime.utcnow()
                if ( t_now - t_out ).total_seconds() >= WAVELEN_OUT:
                    self.output_status(); t_out = t_now
            
            # Restart if file change detected
            t_now   = datetime.utcnow()
            if ( t_now - t_mtime ).total_seconds() > WAVELEN_MTIME_CHK:
                t_mtime = t_now
                if getmtime( __file__ ) > self.this_mtime:
                    self.restart()
            
            t_now       = datetime.utcnow()
            looptime    = ( t_now - t_loop ).total_seconds()
            
            # Estimate mean looptime
            w1  = EWMA_WGT_LOOPTIME
            w2  = 1.0 - w1
            t1  = looptime
            t2  = self.mean_looptime
            
            self.mean_looptime = w1 * t1 + w2 * t2
            
            t_loop      = t_now
            sleep_time  = MIN_LOOP_TIME - looptime
            if sleep_time > 0:
                time.sleep( sleep_time )
            if self.monitor:
                time.sleep( WAVELEN_OUT )

            
    def run_first( self ):
        
        self.create_client()
        self.client.cancelall()
        self.logger = get_logger( 'root', LOG_LEVEL )
        # Get all futures contracts
        self.get_futures()
        self.this_mtime = getmtime( __file__ )
        self.symbols    = [ BTC_SYMBOL ] + list( self.futures.keys()); self.symbols.sort()
        self.deltas     = OrderedDict( { s: None for s in self.symbols } )
        
        # Create historical time series data for estimating vol
        ts_keys = self.symbols + [ 'timestamp' ]; ts_keys.sort()
        
        self.ts = [
            OrderedDict( { f: None for f in ts_keys } ) for i in range( NLAGS + 1 )
        ]
        
        self.vols   = OrderedDict( { s: VOL_PRIOR for s in self.symbols } )
        
        self.start_time         = datetime.utcnow()
        self.update_status()
        self.equity_usd_init    = self.equity_usd
        self.equity_btc_init    = self.equity_btc
    
    
    def update_status( self ):
        
        account = self.client.account()
        spot    = self.get_spot()

        self.equity_btc = account[ 'equity' ]
        self.equity_usd = self.equity_btc * spot
                
        self.update_positions()
                
        self.deltas = OrderedDict( 
            { k: self.positions[ k ][ 'sizeBtc' ] for k in self.futures.keys()}
        )
        self.deltas[ BTC_SYMBOL ] = account[ 'equity' ]        
        
        
    def update_positions( self ):

        self.positions  = OrderedDict( { f: {
            'size':         0,
            'sizeBtc':      0,
            'indexPrice':   None,
            'markPrice':    None
        } for f in self.futures.keys() } )
        positions       = self.client.positions()
        
        for pos in positions:
            if pos[ 'instrument' ] in self.futures:
                self.positions[ pos[ 'instrument' ]] = pos
        
    
    def update_timeseries( self ):
        
        if self.monitor:
            return None
        
        for t in range( NLAGS, 0, -1 ):
            self.ts[ t ]    = cp.deepcopy( self.ts[ t - 1 ] )
        
        spot                    = self.get_spot()
        self.ts[ 0 ][ BTC_SYMBOL ]    = spot
       
        for c in self.futures.keys():
            
            bbo = self.get_bbo( c )
            bid = bbo[ 'bid' ]
            ask = bbo[ 'ask' ]

            if not bid is None and not ask is None:
                mid = 0.5 * ( bbo[ 'bid' ] + bbo[ 'ask' ] )
            else:
                continue
            self.ts[ 0 ][ c ]               = mid
                
        self.ts[ 0 ][ 'timestamp' ]  = datetime.utcnow()

        
    def update_vols( self ):
        
        if self.monitor:
            return None
        
        w   = EWMA_WGT_COV
        ts  = self.ts
        
        t   = [ ts[ i ][ 'timestamp' ] for i in range( NLAGS + 1 ) ]
        p   = { c: None for c in self.vols.keys() }
        for c in ts[ 0 ].keys():
            p[ c ] = [ ts[ i ][ c ] for i in range( NLAGS + 1 ) ]
        
        if any( x is None for x in t ):
            return None
        for c in self.vols.keys():
            if any( x is None for x in p[ c ] ):
                return None
        
        NSECS   = SECONDS_IN_YEAR
        cov_cap = COV_RETURN_CAP / NSECS
        
        for s in self.vols.keys():
            
            x   = p[ s ]            
            dx  = x[ 0 ] / x[ 1 ] - 1
            dt  = ( t[ 0 ] - t[ 1 ] ).total_seconds()
            v   = min( dx ** 2 / dt, cov_cap ) * NSECS
            v   = w * v + ( 1 - w ) * self.vols[ s ] ** 2
            
            self.vols[ s ] = math.sqrt( v )
                            
        
if __name__ == '__main__':
    
    try:
        mmbot = MarketMaker( monitor = args.monitor, output = args.output )
        mmbot.run()
    except( KeyboardInterrupt, SystemExit ):
        #print( "Cancelling open orders" )
        mmbot.client.cancelall()
        sys.exit()
    except:
        print( traceback.format_exc())
        if args.restart:
            mmbot.restart()
        
