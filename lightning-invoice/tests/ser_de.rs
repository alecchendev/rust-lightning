extern crate bitcoin_hashes;
extern crate lightning;
extern crate lightning_invoice;
extern crate secp256k1;

use bitcoin_hashes::hex::FromHex;
use bitcoin_hashes::sha256;
use lightning::ln::PaymentSecret;
use lightning_invoice::*;
use secp256k1::Secp256k1;
use secp256k1::key::SecretKey;
use secp256k1::recovery::{RecoverableSignature, RecoveryId};
use std::time::{Duration, UNIX_EPOCH};
use std::str::FromStr;

// TODO: add more of the examples from BOLT11 and generate ones causing SemanticErrors

fn get_test_tuples() -> Vec<(String, SignedRawInvoice, Option<SemanticError>)> {
	vec![
		(
			"lnbc1pvjluezpp5qqqsyqcyq5rqwzqfqqqsyqcyq5rqwzqfqqqsyqcyq5rqwzqfqypqdpl2pkx2ctnv5sxxmmw\
			wd5kgetjypeh2ursdae8g6twvus8g6rfwvs8qun0dfjkxaq8rkx3yf5tcsyz3d73gafnh3cax9rn449d9p5uxz9\
			ezhhypd0elx87sjle52x86fux2ypatgddc6k63n7erqz25le42c4u4ecky03ylcqca784w".to_owned(),
			InvoiceBuilder::new(Currency::Bitcoin)
				.timestamp(UNIX_EPOCH + Duration::from_secs(1496314658))
				.payment_hash(sha256::Hash::from_hex(
						"0001020304050607080900010203040506070809000102030405060708090102"
				).unwrap())
				.description("Please consider supporting this project".to_owned())
				.build_raw()
				.unwrap()
				.sign(|_| {
					RecoverableSignature::from_compact(
						& [
							0x38u8, 0xec, 0x68, 0x91, 0x34, 0x5e, 0x20, 0x41, 0x45, 0xbe, 0x8a,
							0x3a, 0x99, 0xde, 0x38, 0xe9, 0x8a, 0x39, 0xd6, 0xa5, 0x69, 0x43,
							0x4e, 0x18, 0x45, 0xc8, 0xaf, 0x72, 0x05, 0xaf, 0xcf, 0xcc, 0x7f,
							0x42, 0x5f, 0xcd, 0x14, 0x63, 0xe9, 0x3c, 0x32, 0x88, 0x1e, 0xad,
							0x0d, 0x6e, 0x35, 0x6d, 0x46, 0x7e, 0xc8, 0xc0, 0x25, 0x53, 0xf9,
							0xaa, 0xb1, 0x5e, 0x57, 0x38, 0xb1, 0x1f, 0x12, 0x7f
						],
						RecoveryId::from_i32(0).unwrap()
					)
				}).unwrap(),
			None
		),
		(
			"lnbc2500u1pvjluezpp5qqqsyqcyq5rqwzqfqqqsyqcyq5rqwzqfqqqsyqcyq5rqwzqfqypqdq5xysxxatsyp3\
			k7enxv4jsxqzpuaztrnwngzn3kdzw5hydlzf03qdgm2hdq27cqv3agm2awhz5se903vruatfhq77w3ls4evs3ch\
			9zw97j25emudupq63nyw24cg27h2rspfj9srp".to_owned(),
			InvoiceBuilder::new(Currency::Bitcoin)
				.amount_milli_satoshis(250_000_000)
				.timestamp(UNIX_EPOCH + Duration::from_secs(1496314658))
				.payment_hash(sha256::Hash::from_hex(
					"0001020304050607080900010203040506070809000102030405060708090102"
				).unwrap())
				.description("1 cup coffee".to_owned())
				.expiry_time(Duration::from_secs(60))
				.build_raw()
				.unwrap()
				.sign(|_| {
					RecoverableSignature::from_compact(
						& [
							0xe8, 0x96, 0x39, 0xba, 0x68, 0x14, 0xe3, 0x66, 0x89, 0xd4, 0xb9, 0x1b,
							0xf1, 0x25, 0xf1, 0x03, 0x51, 0xb5, 0x5d, 0xa0, 0x57, 0xb0, 0x06, 0x47,
							0xa8, 0xda, 0xba, 0xeb, 0x8a, 0x90, 0xc9, 0x5f, 0x16, 0x0f, 0x9d, 0x5a,
							0x6e, 0x0f, 0x79, 0xd1, 0xfc, 0x2b, 0x96, 0x42, 0x38, 0xb9, 0x44, 0xe2,
							0xfa, 0x4a, 0xa6, 0x77, 0xc6, 0xf0, 0x20, 0xd4, 0x66, 0x47, 0x2a, 0xb8,
							0x42, 0xbd, 0x75, 0x0e
						],
						RecoveryId::from_i32(1).unwrap()
					)
				}).unwrap(),
			None
		),
		(
			"lnbc20m1pvjluezpp5qqqsyqcyq5rqwzqfqqqsyqcyq5rqwzqfqqqsyqcyq5rqwzqfqypqhp58yjmdan79s6qq\
			dhdzgynm4zwqd5d7xmw5fk98klysy043l2ahrqscc6gd6ql3jrc5yzme8v4ntcewwz5cnw92tz0pc8qcuufvq7k\
			hhr8wpald05e92xw006sq94mg8v2ndf4sefvf9sygkshp5zfem29trqq2yxxz7".to_owned(),
			InvoiceBuilder::new(Currency::Bitcoin)
				.amount_milli_satoshis(2_000_000_000)
				.timestamp(UNIX_EPOCH + Duration::from_secs(1496314658))
				.payment_hash(sha256::Hash::from_hex(
					"0001020304050607080900010203040506070809000102030405060708090102"
				).unwrap())
				.description_hash(sha256::Hash::from_hex(
					"3925b6f67e2c340036ed12093dd44e0368df1b6ea26c53dbe4811f58fd5db8c1"
				).unwrap())
				.build_raw()
				.unwrap()
				.sign(|_| {
					RecoverableSignature::from_compact(
						& [
							0xc6, 0x34, 0x86, 0xe8, 0x1f, 0x8c, 0x87, 0x8a, 0x10, 0x5b, 0xc9, 0xd9,
							0x59, 0xaf, 0x19, 0x73, 0x85, 0x4c, 0x4d, 0xc5, 0x52, 0xc4, 0xf0, 0xe0,
							0xe0, 0xc7, 0x38, 0x96, 0x03, 0xd6, 0xbd, 0xc6, 0x77, 0x07, 0xbf, 0x6b,
							0xe9, 0x92, 0xa8, 0xce, 0x7b, 0xf5, 0x00, 0x16, 0xbb, 0x41, 0xd8, 0xa9,
							0xb5, 0x35, 0x86, 0x52, 0xc4, 0x96, 0x04, 0x45, 0xa1, 0x70, 0xd0, 0x49,
							0xce, 0xd4, 0x55, 0x8c
						],
						RecoveryId::from_i32(0).unwrap()
					)
				}).unwrap(),
			None
		),
		(
			"lnbc20m1pvjluezpp5qqqsyqcyq5rqwzqfqqqsyqcyq5rqwzqfqqqsyqcyq5rqwzqfqypqdq5vdhkven9v5sxyetpdeessp59g4z52329g4z52329g4z52329g4z52329g4z52329g4z52329g4q9qrsgqzfhag3vsafx4e5qssalvw4rn0phsvpp3e5h2xxyk9l8fxsutvndx9t840dqvdrlu2gqmk0q8apqrgnjy9amc07hmjl9e9yzqjks5w2gqgjnyms".to_owned(),
			InvoiceBuilder::new(Currency::Bitcoin)
				.payment_hash(sha256::Hash::from_hex(
					"0001020304050607080900010203040506070809000102030405060708090102"
				).unwrap())
				.description("coffee beans".to_string())
				.amount_milli_satoshis(2_000_000_000)
				.timestamp(UNIX_EPOCH + Duration::from_secs(1496314658))
				.payment_secret(PaymentSecret([42; 32]))
				.build_raw()
				.unwrap()
				.sign::<_, ()>(|msg_hash| {
					let privkey = SecretKey::from_slice(&[41; 32]).unwrap();
					let secp_ctx = Secp256k1::new();
					Ok(secp_ctx.sign_recoverable(msg_hash, &privkey))
				})
				.unwrap(),
			None
		)
	]
}


#[test]
fn serialize() {
	for (serialized, deserialized, _) in get_test_tuples() {
		assert_eq!(deserialized.to_string(), serialized);
	}
}

#[test]
fn deserialize() {
	for (serialized, deserialized, maybe_error) in get_test_tuples() {
		let parsed = serialized.parse::<SignedRawInvoice>().unwrap();

		assert_eq!(parsed, deserialized);

		let validated = Invoice::from_signed(parsed);

		if let Some(error) = maybe_error {
			assert_eq!(Err(error), validated);
		} else {
			assert!(validated.is_ok());
		}
	}
}

#[test]
fn test_bolt_invalid_invoices() {
	// Tests the BOLT 11 invalid invoice test vectors
	assert_eq!(Invoice::from_str(
		"lnbc25m1pvjluezpp5qqqsyqcyq5rqwzqfqqqsyqcyq5rqwzqfqqqsyqcyq5rqwzqfqypqdq5vdhkven9v5sxyetpdeessp5zyg3zyg3zyg3zyg3zyg3zyg3zyg3zyg3zyg3zyg3zyg3zyg3zygs9q4psqqqqqqqqqqqqqqqpqsqq40wa3khl49yue3zsgm26jrepqr2eghqlx86rttutve3ugd05em86nsefzh4pfurpd9ek9w2vp95zxqnfe2u7ckudyahsa52q66tgzcp6t2dyk"
		), Err(ParseOrSemanticError::SemanticError(SemanticError::InvalidFeatures)));
	assert_eq!(Invoice::from_str(
		"lnbc2500u1pvjluezpp5qqqsyqcyq5rqwzqfqqqsyqcyq5rqwzqfqqqsyqcyq5rqwzqfqypqdpquwpc4curk03c9wlrswe78q4eyqc7d8d0xqzpuyk0sg5g70me25alkluzd2x62aysf2pyy8edtjeevuv4p2d5p76r4zkmneet7uvyakky2zr4cusd45tftc9c5fh0nnqpnl2jfll544esqchsrnt"
		), Err(ParseOrSemanticError::ParseError(ParseError::Bech32Error(bech32::Error::InvalidChecksum))));
	assert_eq!(Invoice::from_str(
		"pvjluezpp5qqqsyqcyq5rqwzqfqqqsyqcyq5rqwzqfqqqsyqcyq5rqwzqfqypqdpquwpc4curk03c9wlrswe78q4eyqc7d8d0xqzpuyk0sg5g70me25alkluzd2x62aysf2pyy8edtjeevuv4p2d5p76r4zkmneet7uvyakky2zr4cusd45tftc9c5fh0nnqpnl2jfll544esqchsrny"
		), Err(ParseOrSemanticError::ParseError(ParseError::Bech32Error(bech32::Error::MissingSeparator))));
	assert_eq!(Invoice::from_str(
		"LNBC2500u1pvjluezpp5qqqsyqcyq5rqwzqfqqqsyqcyq5rqwzqfqqqsyqcyq5rqwzqfqypqdpquwpc4curk03c9wlrswe78q4eyqc7d8d0xqzpuyk0sg5g70me25alkluzd2x62aysf2pyy8edtjeevuv4p2d5p76r4zkmneet7uvyakky2zr4cusd45tftc9c5fh0nnqpnl2jfll544esqchsrny"
		), Err(ParseOrSemanticError::ParseError(ParseError::Bech32Error(bech32::Error::MixedCase))));
	assert_eq!(Invoice::from_str(
		"lnbc2500u1pvjluezpp5qqqsyqcyq5rqwzqfqqqsyqcyq5rqwzqfqqqsyqcyq5rqwzqfqypqdq5xysxxatsyp3k7enxv4jsxqzpuaxtrnwngzn3kdzw5hydlzf03qdgm2hdq27cqv3agm2awhz5se903vruatfhq77w3ls4evs3ch9zw97j25emudupq63nyw24cg27h2rspk28uwq"
		), Err(ParseOrSemanticError::SemanticError(SemanticError::InvalidSignature)));
	assert_eq!(Invoice::from_str(
		"lnbc1pvjluezpp5qqqsyqcyq5rqwzqfqqqsyqcyq5rqwzqfqqqsyqcyq5rqwzqfqypqdpl2pkx2ctnv5sxxmmwwd5kgetjypeh2ursdae8g6na6hlh"
		), Err(ParseOrSemanticError::ParseError(ParseError::TooShortDataPart)));
	assert_eq!(Invoice::from_str(
		"lnbc2500x1pvjluezpp5qqqsyqcyq5rqwzqfqqqsyqcyq5rqwzqfqqqsyqcyq5rqwzqfqypqdq5xysxxatsyp3k7enxv4jsxqzpujr6jxr9gq9pv6g46y7d20jfkegkg4gljz2ea2a3m9lmvvr95tq2s0kvu70u3axgelz3kyvtp2ywwt0y8hkx2869zq5dll9nelr83zzqqpgl2zg"
		), Err(ParseOrSemanticError::ParseError(ParseError::UnknownSiPrefix)));
	assert_eq!(Invoice::from_str(
		"lnbc2500000001p1pvjluezpp5qqqsyqcyq5rqwzqfqqqsyqcyq5rqwzqfqqqsyqcyq5rqwzqfqypqdq5xysxxatsyp3k7enxv4jsxqzpu7hqtk93pkf7sw55rdv4k9z2vj050rxdr6za9ekfs3nlt5lr89jqpdmxsmlj9urqumg0h9wzpqecw7th56tdms40p2ny9q4ddvjsedzcplva53s"
		), Err(ParseOrSemanticError::SemanticError(SemanticError::ImpreciseAmount)));
}
